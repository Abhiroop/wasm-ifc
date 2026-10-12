{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

{- | The typed function references of WebAssembly 3.0, checked on the module as it is written.

  The typed program knows a reference by its kind alone: to a function, to an external value,
  to an exception ('Syntax.Types.ValType'). A module says more: whether a reference may be
  null, and of which function type a function is ('Syntax.Types.WrittenType'). The
  specification types a module with what it says, by subtyping (a reference that is not null
  may go where one that may be null is expected, and a function of a type where any function
  is), and asks that a local whose type has no default value be written before it is read.

  This module checks exactly that, with the specification's validation algorithm over the
  types as written: a stack of types, and a stack of frames for the blocks. It decides nothing
  about security, and nothing the typed program relies on. The typed program is built
  afterwards from the erased types, in which every reference may be null and a function
  reference may be of any type; it finds out both when it uses a reference, as @call_indirect@
  always has. So a module this check wrongly accepted would trap where the specification
  promised it could not; it would not go wrong.

  A module that passes comes back without the notes of what it wrote ('Precisely'), which
  nothing after this reads. It keeps the written types of what it declares, for the comparison
  of an import with what another module exports ('Syntax.Module.Interface').
-}
module Validation.References (
    checkReferences,
) where

import Control.Applicative ((<|>))
import Control.Monad (forM_, unless, void, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, gets, modify', put)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Data.Singletons (fromSing)
import Data.Word (Word32)

import Syntax.Functions (RawFunction (..))
import Syntax.Globals (RawGlobal (..))
import Syntax.Immediates (MemArg (..))
import Syntax.Indices
import Syntax.Instructions
import Syntax.Module (ElemMode (..), RawDataSegment (..), RawElementSegment (..), RawMemory (..), RawModule (..), RawTable (..), Written (..))
import Syntax.Module qualified as Module
import Syntax.Types
import Syntax.Vector (SomeVectorOp (..))

{- | Check a decoded module's reference types as written, and take the notes off. A module
  built in Haskell has no written types and is as it is.
-}
checkReferences :: RawModule -> Either String RawModule
checkReferences m = case m.written of
    Nothing -> Right m
    Just w -> do
        let env = environment m w
        forM_ (zip [0 ..] w.types) $ \(i, FuncType params results) -> mapM_ (known (i :: Int)) (params ++ results)
        mapM_ (known (length w.types)) (concat w.locals ++ w.globals ++ w.tables)
        -- A table whose entries cannot be null would need an initial value for them, which is not provided.
        when (any cannotBeNull (drop (length m.stateImports.tables) w.tables)) (Left "type mismatch: a table of references that cannot be null, without an initial value")
        forM_ (zip (drop (length m.stateImports.globals) m.globals) (drop (length m.stateImports.globals) w.globals)) $ \(global, declared) ->
            initialiser env global.initializer >>= \given -> unless (maybe True (\t -> below env t declared) given) (Left "type mismatch: the initial value of a global")
        forM_ (zip3 [length m.imports ..] m.functions w.locals) $ \(index, function, locals) -> checkFunction env index function locals
        Right (withoutNotes m)

cannotBeNull :: WrittenType -> Bool
cannotBeNull t = case t of
    RefTo nullable _ -> not nullable
    Plain _ -> False

-- | A written type names only function types that exist (and, in the type section, earlier ones).
known :: Int -> WrittenType -> Either String ()
known bound t = case t of
    RefTo _ (OfType i) | fromIntegral i >= bound -> Left "unknown type"
    _ -> Right ()

-- *** What the module declares ***

data Env = Env
    { types :: [FuncTypeOf WrittenType]
    , canonical :: [Int]
    -- ^ for each function type, the index of the first type that is the same type
    , functions :: [Word32]
    , globals :: [WrittenType]
    , tables :: [(WrittenType, AddrType)]
    , memories :: [AddrType]
    , tags :: [[WrittenType]]
    -- ^ what an exception of each tag carries
    }

environment :: RawModule -> Written -> Env
environment m w =
    Env
        { types = w.types
        , canonical = canonicalTypes w.types
        , functions = w.functions
        , globals = w.globals
        , tables = zip w.tables [table.addrType | table <- m.tables]
        , memories = [addresses | RawMemory (MemType addresses _) <- m.memories]
        , tags = [maybe [] (\(FuncType params _) -> params) (nth w.types index) | index <- w.tags]
        }

{- | Two function types are the same type if they are written alike, up to the names of the
  types they mention (the specification's equivalence; without recursive types a type mentions
  earlier ones only).
-}
canonicalTypes :: [FuncTypeOf WrittenType] -> [Int]
canonicalTypes = go [] []
  where
    go _ canon [] = reverse canon
    go seen canon (FuncType params results : rest) =
        let renamed = FuncType (map (rename (reverse canon)) params) (map (rename (reverse canon)) results)
            index = fromMaybe (length seen) (elemIndex renamed seen)
         in go (seen ++ [renamed]) (index : canon) rest
    rename canon t = case t of
        RefTo nullable (OfType i) | Just c <- nth canon i -> RefTo nullable (OfType (fromIntegral c))
        _ -> t

nth :: Integral i => [a] -> i -> Maybe a
nth xs i = case drop (fromIntegral i) xs of
    x : _ | i >= 0 -> Just x
    _ -> Nothing

-- | @below env a b@: a value of type @a@ may go where one of type @b@ is expected.
below :: Env -> WrittenType -> WrittenType -> Bool
below env a b = case (a, b) of
    (Plain x, Plain y) -> x == y
    (RefTo nullable heap, RefTo nullable' heap') -> (not nullable || nullable') && heapBelow heap heap'
    _ -> False
  where
    heapBelow heap heap' = case (heap, heap') of
        (OfType i, OfType j) -> nth env.canonical i == nth env.canonical j
        (OfType _, AnyFunction) -> True
        (NoFunction, AnyFunction) -> True
        (NoFunction, OfType _) -> True
        (NoExtern, AnyExtern) -> True
        (NoException, AnyException) -> True
        _ -> heap == heap'

-- | The type of a constant expression that initialises a reference, if it is one this check reads.
initialiser :: Env -> RawExpr -> Either String (Maybe WrittenType)
initialiser env expr = case expr of
    [Precisely (NullOf heap) _] -> Right (Just (RefTo True heap))
    [RefFunc (FunctionIdx f)] -> Just . RefTo False . OfType <$> note "unknown function" (nth env.functions f)
    [GlobalGet (GlobalIdx g)] -> Just <$> note "unknown global" (nth env.globals g)
    _ -> Right Nothing

note :: String -> Maybe a -> Either String a
note message = maybe (Left message) Right

-- *** One function body ***

-- | A block being checked: what a branch to it carries, the height of the stack below it, and whether the rest of it cannot be reached.
data Frame = Frame
    { target :: [WrittenType]
    , height :: Int
    , unreachable :: Bool
    }

-- | The types on the stack, top first ('Nothing' where unreachable code left any type), the frames, innermost first, and the locals that are set.
data Checking = Checking
    { stack :: [Maybe WrittenType]
    , frames :: [Frame]
    , set :: IntSet
    }

type Check = StateT Checking (Either String)

failing :: String -> Check a
failing = lift . Left

checkFunction :: Env -> Int -> RawFunction -> [WrittenType] -> Either String ()
checkFunction env index function declared = do
    FuncType params results <- note "unknown type" (nth env.functions index >>= nth env.types)
    let locals = params ++ declared
        -- (A parameter is set; a local with a default value is set to it; another is not set.)
        initially = IntSet.fromList [i | (i, t) <- zip [0 ..] locals, i < length params || defaultable t]
    evalStateT (framed env locals results results [] results function.body) (Checking [] [] initially)
  where
    defaultable t = case t of
        RefTo nullable _ -> nullable
        Plain _ -> True

push :: Maybe WrittenType -> Check ()
push t = modify' (\s -> s {stack = t : s.stack})

pushAll :: [WrittenType] -> Check ()
pushAll = mapM_ (push . Just)

pop :: Check (Maybe WrittenType)
pop = do
    s <- get
    case s.frames of
        frame : _ | length s.stack == frame.height -> if frame.unreachable then pure Nothing else failing "type mismatch: the stack is empty"
        _ -> case s.stack of
            t : rest -> put s {stack = rest} >> pure t
            [] -> failing "type mismatch: the stack is empty"

expect :: Env -> WrittenType -> Check ()
expect env t = pop >>= \found -> unless (maybe True (\actual -> below env actual t) found) (failing "type mismatch")

-- | Pop values of the types given in the order they were pushed.
expectAll :: Env -> [WrittenType] -> Check ()
expectAll env = mapM_ (expect env) . reverse

popReference :: Check (Maybe WrittenType)
popReference =
    pop >>= \found -> case found of
        Just (Plain _) -> failing "type mismatch: a reference is expected"
        _ -> pure found

nonNull :: WrittenType -> WrittenType
nonNull t = case t of
    RefTo _ heap -> RefTo False heap
    Plain _ -> t

-- | The rest of the block cannot be reached: its stack takes any type.
diverge :: Check ()
diverge = modify' $ \s -> case s.frames of
    frame : outer -> s {stack = drop (length s.stack - frame.height) s.stack, frames = frame {unreachable = True} : outer}
    [] -> s

targetOf :: LabelIdx -> Check [WrittenType]
targetOf (LabelIdx l) = gets (.frames) >>= \frames -> maybe (failing "unknown label") (pure . (.target)) (nth frames l)

{- | A block: its parameters come off the stack, its body is checked in a frame of its own from
  them to its results, and the results go on. The locals a block set are not set after it.
-}
framed :: Env -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [RawInstr] -> Check ()
framed env locals functionResults carried params results body = do
    expectAll env params
    inside env locals functionResults carried params results body
    pushAll results

inside :: Env -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [WrittenType] -> [RawInstr] -> Check ()
inside env locals functionResults carried params results body = do
    before <- get
    put before {frames = Frame carried (length before.stack) False : before.frames}
    pushAll params
    mapM_ (step env locals functionResults Nothing) body
    expectAll env results
    after <- get
    when (length after.stack /= length before.stack) (failing "type mismatch: values are left on the stack")
    put after {frames = before.frames, set = before.set}

step :: Env -> [WrittenType] -> [WrittenType] -> Maybe WrittenNote -> RawInstr -> Check ()
step env locals functionResults written instr = case instr of
    Precisely what inner -> step env locals functionResults (Just what) inner
    Annotated _ inner -> step env locals functionResults written inner
    AtSite _ inner -> step env locals functionResults written inner
    Relabel _ -> pure ()
    Declassify _ -> pure ()
    Unreachable -> diverge
    Nop -> pure ()
    Block blockType body -> blockTypes blockType >>= \(params, results) -> framed env locals functionResults results params results body
    Loop blockType body -> blockTypes blockType >>= \(params, results) -> framed env locals functionResults params params results body
    If blockType thenArm elseArm -> do
        expect env (Plain I32)
        (params, results) <- blockTypes blockType
        expectAll env params
        inside env locals functionResults results params results thenArm
        inside env locals functionResults results params results elseArm
        pushAll results
    TryTable blockType clauses body -> do
        -- A clause branches to a label of the context around the block with what it catches.
        forM_ clauses $ \clause -> do
            (caught, l) <- case clause of
                CatchTag (TagIdx x) l -> (,l) <$> tag x
                CatchTagRef (TagIdx x) l -> (,l) . (++ [RefTo False AnyException]) <$> tag x
                CatchAll l -> pure ([], l)
                CatchAllRef l -> pure ([RefTo False AnyException], l)
            carried <- targetOf l
            unless (length caught == length carried && and (zipWith (below env) caught carried)) (failing "type mismatch: a clause and its label")
        (params, results) <- blockTypes blockType
        framed env locals functionResults results params results body
    Br l -> targetOf l >>= expectAll env >> diverge
    BrIf l -> do
        expect env (Plain I32)
        carried <- targetOf l
        expectAll env carried
        pushAll carried
    BrTable ls fallback -> do
        expect env (Plain I32)
        carried <- targetOf fallback
        forM_ ls $ \l -> do
            other <- targetOf l
            when (length other /= length carried) (failing "type mismatch: the targets of a table take different numbers of values")
            here <- get
            expectAll env other
            put here
        expectAll env carried
        diverge
    Return -> expectAll env functionResults >> diverge
    Call (FunctionIdx f) -> do
        FuncType params results <- functionType f
        expectAll env params
        pushAll results
    ReturnCall (FunctionIdx f) -> do
        FuncType params results <- functionType f
        expectAll env params
        returns results
    CallIndirect (TableIdx t) (TypeIdx ty) -> do
        (entries, addresses) <- table t
        unless (below env entries (RefTo True AnyFunction)) (failing "type mismatch: the table does not hold functions")
        expect env (Plain (addrValType addresses))
        FuncType params results <- typeAt ty
        expectAll env params
        pushAll results
    ReturnCallIndirect (TableIdx t) (TypeIdx ty) -> do
        (entries, addresses) <- table t
        unless (below env entries (RefTo True AnyFunction)) (failing "type mismatch: the table does not hold functions")
        expect env (Plain (addrValType addresses))
        FuncType params results <- typeAt ty
        expectAll env params
        returns results
    CallRef (TypeIdx ty) -> do
        FuncType params results <- typeAt ty
        expect env (RefTo True (OfType ty))
        expectAll env params
        pushAll results
    ReturnCallRef (TypeIdx ty) -> do
        FuncType params results <- typeAt ty
        expect env (RefTo True (OfType ty))
        expectAll env params
        returns results
    Throw (TagIdx x) -> do
        tag x >>= expectAll env
        diverge
    ThrowRef -> expect env (RefTo True AnyException) >> diverge
    LocalGet (LocalIdx i) -> do
        t <- local i
        isSet <- gets (IntSet.member (fromIntegral i) . (.set))
        unless isSet (failing "uninitialized local")
        push (Just t)
    LocalSet (LocalIdx i) -> local i >>= expect env >> setLocal i
    LocalTee (LocalIdx i) -> local i >>= \t -> expect env t >> push (Just t) >> setLocal i
    GlobalGet (GlobalIdx g) -> global g >>= push . Just
    GlobalSet (GlobalIdx g) -> global g >>= expect env
    RefNull t -> case written of
        Just (NullOf heap) -> named (RefTo True heap) >> push (Just (RefTo True heap))
        _ -> push (Just (lifted t))
    RefIsNull -> popReference >> push (Just (Plain I32))
    RefFunc (FunctionIdx f) -> maybe (failing "unknown function") (push . Just . RefTo False . OfType) (nth env.functions f)
    RefAsNonNull -> popReference >>= push . fmap nonNull
    BrOnNull l -> do
        reference <- popReference
        carried <- targetOf l
        expectAll env carried
        pushAll carried
        push (fmap nonNull reference)
    BrOnNonNull l -> do
        carried <- targetOf l
        case reverse carried of
            [] -> failing "type mismatch: the target takes no reference"
            last' : others -> do
                reference <- popReference
                unless (maybe True (\t -> below env (nonNull t) last') reference) (failing "type mismatch")
                expectAll env (reverse others)
                pushAll (reverse others)
    Duplicate -> pop >>= \t -> push t >> push t
    Drop -> void pop
    Select -> do
        expect env (Plain I32)
        first' <- pop
        second <- pop
        case (first', second) of
            (Just (RefTo _ _), _) -> failing "type mismatch: select of a reference needs its type"
            (_, Just (RefTo _ _)) -> failing "type mismatch: select of a reference needs its type"
            (Just a, Just b) | a /= b -> failing "type mismatch"
            _ -> push (first' <|> second)
    SelectTyped ts -> case fromMaybe (map lifted ts) (selected written) of
        [t] -> named t >> expect env (Plain I32) >> expect env t >> expect env t >> push (Just t)
        _ -> failing "invalid result arity"
    TableGet (TableIdx t) -> table t >>= \(entries, addresses) -> expect env (Plain (addrValType addresses)) >> push (Just entries)
    TableSet (TableIdx t) -> table t >>= \(entries, addresses) -> expect env entries >> expect env (Plain (addrValType addresses))
    TableSize (TableIdx t) -> table t >>= \(_, addresses) -> push (Just (Plain (addrValType addresses)))
    TableGrow (TableIdx t) -> table t >>= \(entries, addresses) -> expect env (Plain (addrValType addresses)) >> expect env entries >> push (Just (Plain (addrValType addresses)))
    TableFill (TableIdx t) -> table t >>= \(entries, addresses) -> expect env (Plain (addrValType addresses)) >> expect env entries >> expect env (Plain (addrValType addresses))
    TableCopy (TableIdx to) (TableIdx from) -> do
        (entries, addresses) <- table to
        (entries', addresses') <- table from
        unless (below env entries' entries) (failing "type mismatch: the tables hold different types")
        expect env (Plain (addrValType (smaller addresses addresses')))
        expect env (Plain (addrValType addresses'))
        expect env (Plain (addrValType addresses))
    TableInit _ (TableIdx t) -> table t >>= \(_, addresses) -> expect env (Plain I32) >> expect env (Plain I32) >> expect env (Plain (addrValType addresses))
    ElemDrop _ -> pure ()
    DataDrop _ -> pure ()
    _ -> case plainSignature env instr of
        Just (consumed, produced) -> mapM_ (expect env . Plain) consumed >> mapM_ (push . Just . Plain) produced
        Nothing -> failing "unknown memory"
  where
    selected what = case what of
        Just (SelectOf ts) -> Just ts
        _ -> Nothing
    blockTypes (FuncType params results) = case written of
        Just (BlockOfType i) -> typeAt i >>= \(FuncType ps rs) -> pure (ps, rs)
        Just (BlockResult t) -> named t >> pure ([], [t])
        _ -> pure (map lifted params, map lifted results)
    typeAt i = maybe (failing "unknown type") pure (nth env.types i)
    named t = lift (known (length env.types) t)
    tag x = maybe (failing "unknown tag") pure (nth env.tags x)
    functionType f = maybe (failing "unknown function") pure (nth env.functions f >>= nth env.types)
    table t = maybe (failing "unknown table") pure (nth env.tables t)
    global g = maybe (failing "unknown global") pure (nth env.globals g)
    local i = maybe (failing "unknown local") pure (nth locals i)
    setLocal i = modify' (\s -> s {set = IntSet.insert (fromIntegral i) s.set})
    -- A tail call's results are the function's: each may go where the function's result is expected.
    returns results = do
        unless (length results == length functionResults && and (zipWith (below env) results functionResults)) (failing "type mismatch: the results of a tail call")
        diverge
    smaller a b = if a == AddrI32 || b == AddrI32 then AddrI32 else AddrI64

addrValType :: AddrType -> ValType
addrValType AddrI32 = I32
addrValType AddrI64 = I64

{- | What an instruction that handles no reference takes off the stack, top first, and what it
  puts on it. 'Nothing' for a memory the module has not.
-}
plainSignature :: Env -> RawInstr -> Maybe ([ValType], [ValType])
plainSignature env instr = case instr of
    Const t _ -> Just ([], [fromSing t])
    Add t -> binary t
    Sub t -> binary t
    Mul t -> binary t
    Div t _ -> binary t
    Rem t _ -> binary t
    And t -> binary t
    Or t -> binary t
    Xor t -> binary t
    Shl t -> binary t
    Shr t _ -> binary t
    Rotl t -> binary t
    Rotr t -> binary t
    Min t -> binary t
    Max t -> binary t
    Copysign t -> binary t
    Clz t -> unary t
    Ctz t -> unary t
    Popcnt t -> unary t
    Abs t -> unary t
    Neg t -> unary t
    Sqrt t -> unary t
    Ceil t -> unary t
    Floor t -> unary t
    FloatTrunc t -> unary t
    Nearest t -> unary t
    Eqz t -> Just ([fromSing t], [I32])
    Eq t -> comparison t
    Ne t -> comparison t
    Lt t _ -> comparison t
    Gt t _ -> comparison t
    Le t _ -> comparison t
    Ge t _ -> comparison t
    Convert op -> let (from, to) = convertEnds op in Just ([fromSing (numSing from)], [fromSing (numSing to)])
    Vector (SomeVectorOp operands result _) -> Just (fromSing operands, [fromSing result])
    Load t memArg -> address memArg.memory >>= \at -> Just ([at], [fromSing t])
    LoadN t _ _ memArg -> address memArg.memory >>= \at -> Just ([at], [fromSing t])
    Store t memArg -> address memArg.memory >>= \at -> Just ([fromSing t, at], [])
    StoreN t _ memArg -> address memArg.memory >>= \at -> Just ([fromSing t, at], [])
    VectorLoad _ memArg -> address memArg.memory >>= \at -> Just ([at], [V128])
    VectorStore memArg -> address memArg.memory >>= \at -> Just ([V128, at], [])
    VectorLoadLane _ _ memArg -> address memArg.memory >>= \at -> Just ([V128, at], [V128])
    VectorStoreLane _ _ memArg -> address memArg.memory >>= \at -> Just ([V128, at], [])
    MemorySize (MemoryIdx i) -> address i >>= \at -> Just ([], [at])
    MemoryGrow (MemoryIdx i) -> address i >>= \at -> Just ([at], [at])
    MemoryFill (MemoryIdx i) -> address i >>= \at -> Just ([at, I32, at], [])
    MemoryCopy (MemoryIdx to) (MemoryIdx from) -> do
        at <- address to
        at' <- address from
        Just ([if at == I32 || at' == I32 then I32 else I64, at', at], [])
    MemoryInit _ (MemoryIdx i) -> address i >>= \at -> Just ([I32, I32, at], [])
    _ -> Just ([], [])
  where
    binary t = Just ([fromSing t, fromSing t], [fromSing t])
    unary t = Just ([fromSing t], [fromSing t])
    comparison t = Just ([fromSing t, fromSing t], [I32])
    address i = addrValType <$> nth env.memories i

-- *** Taking the notes off ***

withoutNotes :: RawModule -> RawModule
withoutNotes m =
    m
        { Module.functions = [function {body = plain function.body} | function <- m.functions]
        , Module.globals = [global {initializer = plain global.initializer} | global <- m.globals]
        , elementSegments = [RawElementSegment (plainMode segment.mode) segment.entryType (map plain segment.items) | segment <- m.elementSegments]
        , dataSegments = [RawDataSegment (plainData segment.mode) segment.bytes | segment <- m.dataSegments]
        }
  where
    plainMode mode = case mode of
        ElemActive t offset -> ElemActive t (plain offset)
        other -> other
    plainData mode = case mode of
        Module.Active memory offset -> Module.Active memory (plain offset)
        other -> other

plain :: [RawInstr] -> [RawInstr]
plain = map go
  where
    go instr = case instr of
        Precisely _ inner -> go inner
        Block blockType body -> Block blockType (plain body)
        Loop blockType body -> Loop blockType (plain body)
        If blockType thenArm elseArm -> If blockType (plain thenArm) (plain elseArm)
        TryTable blockType clauses body -> TryTable blockType clauses (plain body)
        Annotated level inner -> Annotated level (go inner)
        AtSite site inner -> AtSite site (go inner)
        _ -> instr
