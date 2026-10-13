{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedDatatypes #-}

{- | The chunks of a memory by their index: a persistent map from chunk index to chunk, which
  is what "Runtime.MemInst" keeps a memory's written chunks in.

  It is a radix tree of fan-out sixteen over the bits of the index, four at a time. A store
  replaces one chunk, which copies the nodes on the way to it, and a node is sixteen pointers:
  GHC allocates and copies an array of that constant size where it is used, by moving the heap
  pointer. In a general map of integers (@IntMap@), finding the chunk and putting one back was
  a quarter of what a store executed and a fifth of a load.

  The tree is as deep as its largest index needs and grows at the root, so a small memory has
  a shallow tree, and one that declares 4 GiB costs nothing until it is written.

  The nodes are an unlifted type: a node is never an unevaluated computation, so the code
  that walks the tree does not check for one. The primitive array operations check no index;
  every index they are given is four bits of the chunk index, so it is inside an array of
  sixteen whatever the chunk index is.
-}
module Runtime.Chunks (
    Chunks,
    noChunks,
    Leaf (Absent, Held),
    chunkAt,
    withChunk,
) where

import Data.Vector.Unboxed qualified as UV
import Data.Word (Word8)
import GHC.Exts (
    Int (I#),
    Int#,
    SmallArray#,
    UnliftedType,
    andI#,
    indexSmallArray#,
    isTrue#,
    newSmallArray#,
    runRW#,
    thawSmallArray#,
    uncheckedIShiftRL#,
    unsafeFreezeSmallArray#,
    writeSmallArray#,
    (+#),
    (-#),
    (/=#),
    (>#),
 )

{- | A node of the tree. At the bottom, where no bits of the index are left, it is a chunk or
  the absence of one; above, sixteen nodes, or 'Absent' for a part where nothing was written.
-}
type Leaf :: UnliftedType
data Leaf
    = Absent
    | Held !(UV.Vector Word8)
    | Sixteen (SmallArray# Leaf)

{- | The written chunks. The number is the shift that takes a chunk index to its four bits at
  the root: the root holds indices below @16 * 2 ^ shift@.
-}
data Chunks = Chunks !Int Leaf

-- | No chunk written.
noChunks :: () -> Chunks
noChunks () = Chunks 0 Absent

-- | Whether an index is past what a tree with this shift at its root holds.
beyond :: Int# -> Int# -> Bool
beyond key shift = isTrue# (uncheckedIShiftRL# key (shift +# 4#) /=# 0#)

{- | The chunk at an index: 'Held', or 'Absent' if nothing was written there.
Inlined, so that the walk down the tree is a loop inside the load that asks for the chunk.
-}
{-# INLINE chunkAt #-}
chunkAt :: Int -> Chunks -> Leaf
chunkAt (I# key) (Chunks (I# rootShift) root)
    | beyond key rootShift = Absent
    | otherwise = descend rootShift root
  where
    descend :: Int# -> Leaf -> Leaf
    descend shift node = case node of
        Sixteen children -> case indexSmallArray# children (uncheckedIShiftRL# key shift `andI#` 15#) of
            (# child #) -> descend (shift -# 4#) child
        found -> found

-- | The chunks with the one at an index replaced.
withChunk :: Int -> UV.Vector Word8 -> Chunks -> Chunks
withChunk (I# key) !chunk (Chunks (I# rootShift) root)
    | beyond key rootShift = withChunk (I# key) chunk (Chunks (I# (rootShift +# 4#)) (raised root))
    | otherwise = Chunks (I# rootShift) (put rootShift root)
  where
    -- A tree that holds sixteen times as much: the old one is its first part.
    raised :: Leaf -> Leaf
    raised node = case node of
        Absent -> Absent
        _ -> onlyChild 0# node
    put :: Int# -> Leaf -> Leaf
    put shift node = case node of
        Sixteen children -> case indexSmallArray# children (place shift) of
            (# old #) -> withChild (place shift) (below shift old) children
        _ -> onlyChild (place shift) (below shift Absent)
    place :: Int# -> Int#
    place shift = uncheckedIShiftRL# key shift `andI#` 15#
    -- What goes under a node at this shift, where @old@ was: the chunk, or the rest of the way.
    below :: Int# -> Leaf -> Leaf
    below shift old
        | isTrue# (shift ># 0#) = put (shift -# 4#) old
        | otherwise = Held chunk

-- | Sixteen nodes, one of them replaced.
withChild :: Int# -> Leaf -> SmallArray# Leaf -> Leaf
withChild at child children =
    runRW#
        ( \s0 -> case thawSmallArray# children 0# 16# s0 of
            (# s1, new #) -> case writeSmallArray# new at child s1 of
                s2 -> case unsafeFreezeSmallArray# new s2 of
                    (# _, frozen #) -> Sixteen frozen
        )

-- | Sixteen nodes, all absent but one.
onlyChild :: Int# -> Leaf -> Leaf
onlyChild at child =
    runRW#
        ( \s0 -> case newSmallArray# 16# Absent s0 of
            (# s1, new #) -> case writeSmallArray# new at child s1 of
                s2 -> case unsafeFreezeSmallArray# new s2 of
                    (# _, frozen #) -> Sixteen frozen
        )
