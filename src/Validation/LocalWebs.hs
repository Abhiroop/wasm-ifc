{- | Live-range splitting of local variables, before elaboration. A compiler reuses a WebAssembly
  local for several variables whose lifetimes do not overlap (LLVM's register colouring does so
  in every optimised function), and a local has one label for the whole function, so a local
  that holds a file descriptor first and a byte of a password later would be secret throughout.
  Splitting gives each /web/ of a local its own local: the definitions (@local.set@,
  @local.tee@, and the value a local starts with) that reach a common use, together with those
  uses. The renamed function computes exactly the same values, since every use reads a local
  that only the definitions reaching it write, so noninterference of the renamed function is
  noninterference of the original; and each web now has a label of its own.

  The webs come from reaching definitions over the structured control flow: a branch carries
  the definitions that reach it to its target (a block's end, a loop's start), a loop is
  iterated until the definitions at its start stop growing, and code after an unconditional
  transfer is reached by none. A parameter keeps its index for the web of the value it is
  called with; every other web becomes a declared local of its local's type, in order of first
  definition.
-}
module Validation.LocalWebs (
    splitLocals,
    splitModuleLocals,
) where

import Control.Monad (forM_, when)
import Control.Monad.Trans.State.Strict (State, evalState, execState, get, gets, modify', put)
import Data.Graph (buildG, components)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import Data.Tree (flatten)
import Data.Word (Word32)

import Syntax.Functions (RawFunction (..))
import Syntax.Indices (LabelIdx (..), LocalIdx (..))
import Syntax.Instructions (RawInstr (..))
import Syntax.Module (RawModule (..))
import Syntax.Types (FuncTypeOf (..))

-- | The occurrences of locals in a body and the control flow between them, numbered in code order.
data Node
    = -- | a @local.get@: its use number and local
      Use Int Int
    | -- | a @local.set@ or @local.tee@: its definition number and local
      Define Int Int
    | BlockNode [Node]
    | LoopNode [Node]
    | IfNode [Node] [Node]
    | Branch Int
    | BranchIf Int
    | BranchTable [Int]
    | -- | @return@ or @unreachable@: control leaves the body
      Leave
    | Other

-- | The definitions that may have written each local at a point, or 'Nothing' where no control reaches.
type Reaching = Maybe (IntMap IntSet)

-- | What the analysis gathers: the definitions reaching each use, and what reaches each enclosing label (innermost first).
data Flow = Flow
    { reachingUses :: IntMap IntSet
    , atLabels :: [Reaching]
    }

{- | Split the locals of a function into its webs. The first definitions, numbered from zero,
  are the values the locals start with (the arguments, then the declared locals' zeros).
-}
splitLocals :: RawFunction -> RawFunction
splitLocals function@(RawFunction signature declared body)
    -- A body that names a local the function does not have is invalid; validation rejects it as written.
    | any (>= localCount) (IntMap.elems definitionLocals ++ map snd (useLocals nodes)) = function
    | otherwise = RawFunction signature newDeclared (evalState (rename webOfDefinition webOfUse body) (localCount, 0))
  where
    FuncType params _ = signature
    localTypes = params ++ declared
    localCount = length localTypes
    nodes = evalState (number body) (localCount, 0)
    definitionLocals = definitions localCount nodes
    definitionCount = IntMap.size definitionLocals
    Flow {reachingUses = uses} = execState (analyse nodes (Just initial)) (Flow IntMap.empty [Nothing])
    initial = IntMap.fromList [(i, IntSet.singleton i) | i <- [0 .. localCount - 1]]
    -- Webs: the definitions connected by a common use.
    graph = buildG (0, definitionCount - 1) [(d, d') | defs <- IntMap.elems uses, d : rest <- [IntSet.toAscList defs], d' <- rest]
    webs = map (IntSet.fromList . flatten) (components graph)
    webOf = IntMap.fromList [(d, web) | (web, members) <- zip [0 :: Int ..] webs, d <- IntSet.toList members]
    -- A parameter's starting web keeps the parameter's index; the others are declared in order of first definition.
    starting = IntMap.fromList [(webOf IntMap.! p, fromIntegral p) | p <- [0 .. length params - 1]]
    -- A declared local's starting zero that nothing reads needs no local of its own.
    others = [(web, IntSet.findMin members) | (web, members) <- zip [0 ..] webs, not (IntMap.member web starting), not (unreadZero members)]
    unreadZero members = IntSet.size members == 1 && IntSet.findMin members < localCount && not (IntSet.member (IntSet.findMin members) readDefinitions)
    readDefinitions = IntSet.unions (IntMap.elems uses) <> IntSet.fromList [local | (u, local) <- useLocals nodes, not (IntMap.member u uses)]
    ordered = map fst (sortOn snd others)
    fresh = IntMap.fromList (zip ordered [fromIntegral (length params) ..])
    indexOfWeb web = fromMaybe (fresh IntMap.! web) (IntMap.lookup web starting)
    newDeclared = [localTypes !! (definitionLocals IntMap.! IntSet.findMin (webs !! web)) | web <- ordered]
    webOfDefinition d = indexOfWeb (webOf IntMap.! d)
    -- A use no definition reaches is never run; it reads its local's starting web.
    webOfUse u local = case IntSet.minView (IntMap.findWithDefault IntSet.empty u uses) of
        Just (d, _) -> webOfDefinition d
        Nothing -> webOfDefinition local

-- | Every use and the local it reads.
useLocals :: [Node] -> [(Int, Int)]
useLocals = concatMap collect
  where
    collect node = case node of
        Use u local -> [(u, local)]
        BlockNode body -> useLocals body
        LoopNode body -> useLocals body
        IfNode thenBody elseBody -> useLocals thenBody ++ useLocals elseBody
        _ -> []

-- | Every function of a module with its locals split ('splitLocals').
splitModuleLocals :: RawModule -> RawModule
splitModuleLocals m =
    RawModule
        { types = m.types
        , imports = m.imports
        , functions = map splitLocals m.functions
        , globals = m.globals
        , memories = m.memories
        , tables = m.tables
        , elementSegments = m.elementSegments
        , dataSegments = m.dataSegments
        , exports = m.exports
        , start = m.start
        , customSections = m.customSections
        }

-- | The local of every definition, the starting values included.
definitions :: Int -> [Node] -> IntMap Int
definitions localCount nodes = IntMap.fromList ([(i, i) | i <- [0 .. localCount - 1]] ++ concatMap collect nodes)
  where
    collect node = case node of
        Define d local -> [(d, local)]
        BlockNode body -> concatMap collect body
        LoopNode body -> concatMap collect body
        IfNode thenBody elseBody -> concatMap collect thenBody ++ concatMap collect elseBody
        _ -> []

-- | Number the definitions and uses in code order (definitions after the starting values).
number :: [RawInstr] -> State (Int, Int) [Node]
number = mapM one
  where
    one raw = case raw of
        LocalGet (LocalIdx i) -> do
            (d, u) <- get
            put (d, u + 1)
            pure (Use u (fromIntegral i))
        LocalSet (LocalIdx i) -> define i
        LocalTee (LocalIdx i) -> define i
        Block _ body -> BlockNode <$> number body
        Loop _ body -> LoopNode <$> number body
        If _ thenBody elseBody -> IfNode <$> number thenBody <*> number elseBody
        Br (LabelIdx l) -> pure (Branch (fromIntegral l))
        BrIf (LabelIdx l) -> pure (BranchIf (fromIntegral l))
        BrTable targets (LabelIdx l) -> pure (BranchTable (fromIntegral l : [fromIntegral t | LabelIdx t <- targets]))
        Return -> pure Leave
        Unreachable -> pure Leave
        _ -> pure Other
    define i = do
        (d, u) <- get
        put (d + 1, u)
        pure (Define d (fromIntegral i))

-- | The same traversal as 'number', renaming every occurrence to the local of its web.
rename :: (Int -> Word32) -> (Int -> Int -> Word32) -> [RawInstr] -> State (Int, Int) [RawInstr]
rename webOfDefinition webOfUse = mapM one
  where
    one raw = case raw of
        LocalGet (LocalIdx i) -> do
            (d, u) <- get
            put (d, u + 1)
            pure (LocalGet (LocalIdx (webOfUse u (fromIntegral i))))
        LocalSet _ -> LocalSet . LocalIdx <$> define
        LocalTee _ -> LocalTee . LocalIdx <$> define
        Block bt body -> Block bt <$> mapM one body
        Loop bt body -> Loop bt <$> mapM one body
        If bt thenBody elseBody -> If bt <$> mapM one thenBody <*> mapM one elseBody
        other -> pure other
    define = do
        (d, u) <- get
        put (d + 1, u)
        pure (webOfDefinition d)

-- | Reaching definitions through a sequence, from what reaches its start to what falls out of its end.
analyse :: [Node] -> Reaching -> State Flow Reaching
analyse [] reaching = pure reaching
analyse (node : rest) reaching = step node reaching >>= analyse rest

step :: Node -> Reaching -> State Flow Reaching
step node reaching = case node of
    Use u local -> do
        forM_ reaching $ \defs ->
            modify' (\flow -> flow {reachingUses = IntMap.insertWith IntSet.union u (IntMap.findWithDefault IntSet.empty local defs) flow.reachingUses})
        pure reaching
    Define d local -> pure (IntMap.insert local (IntSet.singleton d) <$> reaching)
    Branch l -> reach l reaching >> pure Nothing
    BranchIf l -> reach l reaching >> pure reaching
    BranchTable ls -> mapM_ (`reach` reaching) ls >> pure Nothing
    Leave -> pure Nothing
    Other -> pure reaching
    BlockNode body -> withLabel (analyse body reaching) (\out atEnd -> pure (joinReaching out atEnd))
    IfNode thenBody elseBody -> do
        thenOut <- withLabel (analyse thenBody reaching) (\out atEnd -> pure (joinReaching out atEnd))
        elseOut <- withLabel (analyse elseBody reaching) (\out atEnd -> pure (joinReaching out atEnd))
        pure (joinReaching thenOut elseOut)
    LoopNode body -> loopFrom reaching
      where
        loopFrom start = do
            (out, back) <- withLabel (analyse body start) (curry pure)
            let start' = joinReaching start back
            if start' == start then pure out else loopFrom start'

-- | Run the analysis of a body inside a new label, and hand what fell out and what reached the label on.
withLabel :: State Flow Reaching -> (Reaching -> Reaching -> State Flow a) -> State Flow a
withLabel body k = do
    modify' (\flow -> flow {atLabels = Nothing : flow.atLabels})
    out <- body
    labels <- gets (.atLabels)
    case labels of
        atLabel : outer -> do
            modify' (\flow -> flow {atLabels = outer})
            k out atLabel
        [] -> k out Nothing

-- | A branch to the label at this depth: what reaches here reaches it.
reach :: Int -> Reaching -> State Flow ()
reach depth reaching = do
    labels <- gets (.atLabels)
    when (depth < length labels) $
        modify' (\flow -> flow {atLabels = [if k == depth then joinReaching at reaching else at | (k, at) <- zip [0 ..] labels]})

joinReaching :: Reaching -> Reaching -> Reaching
joinReaching Nothing other = other
joinReaching other Nothing = other
joinReaching (Just a) (Just b) = Just (IntMap.unionWith IntSet.union a b)
