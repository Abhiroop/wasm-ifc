{- | Several instances that import from one another: a world of them, with the memories, tables
  and globals that they share.

  The interpreter is pure and an instance owns its state, so nothing here is a pointer that
  two instances hold. What makes sharing work is that only one instance runs at a time, and
  control passes from one to another at two points only: a call out of a module, and its
  return. A memory, a table or a global lives in the instance that defines it, its /home/. An
  instance that imports it takes it from the home whenever control comes to it ('pull') and
  gives it back whenever control leaves it ('push'), by a call out, a return or a trap. Between
  those points nobody else runs, so every instruction sees what the last writer left: the
  semantics of a shared object. Handing over costs nothing, since a memory and a table are
  persistent structures.

  An instance may be entered again while a call out of it waits (the function it called calls
  back). 'Runtime.Module.Instance' keeps one state for all its activations, so the waiting
  one resumes from what the nested one, and whoever wrote to its memory meanwhile, left.

  Inside one instance two indices cannot be one object. A module that imports the same
  memory, the same table or the same writable global twice is therefore rewritten before it is
  validated, so that it uses the object under its first index only ('unaliased'); one that was
  not is not linked ('Runtime.Instantiate.ImportedTwice'). (A tag is a name and holds nothing,
  so it may be imported any number of times.)

  An exception that leaves a function another module called is thrown again in that module,
  where the call was ('Runtime.Module.throwInto'). A tag has one name among all instances, and
  a module that imports a tag knows it by the name of the tag it imports, so a clause for the
  tag catches the exception whichever of the modules threw it.

  A reference to a function names its instance ('Syntax.Immediates.functionReferenceIn'), so
  a table that two modules share holds functions of both, and an indirect call through an
  entry of the other module leaves the module like a call of an import
  ('Runtime.Interpreter.ReferencedBy'). The world compares the function's type with the one
  the call expects, which the calling module cannot do for a function that is not its own.

  Calls between modules carry public values only: an import is typed at public parameters and
  a public bound ('Runtime.Interpreter.ForeignFunc'), and a function whose results its
  module's policy declares secret is not given to other modules, by name or by reference. A
  global and a table are imported at the level they have at home
  ('Runtime.Instantiate.Embedder'), and the bytes of a memory keep their levels wherever it goes.
-}
module Runtime.Link (
    World,
    emptyWorld,
    instantiateIn,
    unaliased,
    register,
    callExport,
    callFunction,
    viewInstance,
) where

import Control.Applicative ((<|>))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Word (Word32, Word64)

import Runtime.Instantiate (Embedder (..), InstantiationError (..), StateImports (..), instantiateUntilStart, moduleInterface, stateImportsOf)
import Runtime.Module
import Runtime.Trap (Trap (..))
import Syntax.Immediates (functionReferent)
import Syntax.Indices (FunctionIdx (..), GlobalIdx (..), MemoryIdx (..), TableIdx (..), TagIdx (..))
import Syntax.Module (Aliases (..), ExportDesc (..), Interface (..), RawModule (..), SomeModule)
import Syntax.Module qualified as Raw (StateImports (..))
import Syntax.Types (FuncType, Mutability (..), ValType, closedBelow)
import Syntax.TypesIFC (SecLevel (..))
import Validation.Aliases (Kind (..), renamed)

-- | Where a shared object lives: the instance that defines it, and its index there.
type Home = (Int, Int)

{- | What an instance imports: for each imported global, memory and table, by its index in the
instance, its home; and the names under which modules were registered when it was linked.
-}
data Bound = Bound
    { globals :: [(Int, Home)]
    , memories :: [(Int, Home)]
    , tables :: [(Int, Home)]
    , names :: Map Text Int
    }

data World = World
    { instances :: IntMap Instance
    , interfaces :: IntMap Interface
    -- ^ the types of each instance's functions, globals and tables as its module wrote them, where it did
    , bound :: IntMap Bound
    , registered :: Map Text Int
    -- ^ the instances modules can import from, by the module name they import
    , next :: Int
    }

emptyWorld :: World
emptyWorld = World IntMap.empty IntMap.empty IntMap.empty Map.empty 0

-- | Make an instance importable under a module name.
register :: Text -> Int -> World -> World
register name x world = world {registered = Map.insert name x world.registered}

{- | An instance as it stands, with what it imports as its homes have it now. (An instance
  holds an imported object as it was when control last left it.)
-}
viewInstance :: World -> Int -> Maybe SomeModuleInst
viewInstance world x = instanceModule <$> IntMap.lookup x (pull x world).instances

-- | What an instance exports under a name, if it is of the kind asked for.
exported :: (ExportDesc -> Maybe index) -> World -> Map Text Int -> Text -> Text -> Maybe (Int, index)
exported kind world names moduleName fieldName = do
    x <- Map.lookup moduleName names
    inst <- IntMap.lookup x world.instances
    index <- exportOf inst fieldName >>= kind
    pure (x, index)

functionExport, globalExport, memoryExport, tableExport, tagExport :: ExportDesc -> Maybe Int
tagExport desc = case desc of ExportTag (TagIdx i) -> Just (fromIntegral i); _ -> Nothing
functionExport desc = case desc of ExportFunc (FunctionIdx i) -> Just (fromIntegral i); _ -> Nothing
globalExport desc = case desc of ExportGlobal (GlobalIdx i) -> Just (fromIntegral i); _ -> Nothing
memoryExport desc = case desc of ExportMem (MemoryIdx i) -> Just (fromIntegral i); _ -> Nothing
tableExport desc = case desc of ExportTable (TableIdx i) -> Just (fromIntegral i); _ -> Nothing

-- | The home of an exported object: the exporter's own, or the one it imports it from.
homeOf :: (ExportDesc -> Maybe Int) -> (Bound -> [(Int, Home)]) -> World -> Map Text Int -> Text -> Text -> Maybe Home
homeOf kind imported world names moduleName fieldName = do
    (x, index) <- exported kind world names moduleName fieldName
    pure (fromMaybe (x, index) (IntMap.lookup x world.bound >>= lookup index . imported))

-- | A function another module may call: one whose results its own module's policy keeps public.
callable :: Instance -> Int -> Maybe FuncType
callable inst index = case functionType inst (fromIntegral index) of
    Just (signature, resultLevels) | all (== Low) resultLevels -> Just signature
    _ -> Nothing

-- | What the world gives a module that is instantiated in it as instance @x@.
embedderIn :: World -> Int -> Embedder
embedderIn world x =
    Embedder
        { instanceNumber = fromIntegral x
        , functions = \moduleName fieldName -> do
            (y, index) <- exported functionExport world world.registered moduleName fieldName
            inst <- IntMap.lookup y world.instances
            callable inst index
        , globals = \moduleName fieldName -> do
            (home, index) <- homeOf globalExport (.globals) world world.registered moduleName fieldName
            IntMap.lookup home world.instances >>= (`globalAt` index)
        , memories = \moduleName fieldName -> do
            (home, index) <- homeOf memoryExport (.memories) world world.registered moduleName fieldName
            IntMap.lookup home world.instances >>= (`memoryAt` index)
        , tables = \moduleName fieldName -> do
            (home, index) <- homeOf tableExport (.tables) world world.registered moduleName fieldName
            IntMap.lookup home world.instances >>= (`tableAt` index)
        , tags = tagNamed world
        }

-- | The tag an instance exports under a name: its name among all instances, and what it carries.
tagNamed :: World -> Text -> Text -> Maybe (Word64, [ValType])
tagNamed world moduleName fieldName = do
    (y, index) <- exported tagExport world world.registered moduleName fieldName
    IntMap.lookup y world.instances >>= (`tagAt` index)

{- | Instantiate a module in the world: its number there, or why not. An error with a number is
  one of an active segment or of the start function: the instance exists, what it wrote before
  the error is written, and its functions stay reachable through the tables it wrote them to.
-}
instantiateIn :: World -> SomeModule -> (World, Either InstantiationError Int, Maybe Int)
instantiateIn world m = case maybe (instantiateUntilStart (embedderIn world x) m) Left (fmap (uncurry ImportedTwice) twice <|> fmap (ImportTypeMismatch . snd) mismatched) of
    Left failure -> (world, Left failure, Nothing)
    Right (inst, failed, start) ->
        -- (An import the module does not use is given once and then left alone.)
        let homes kind imported names = filter ((`notElem` unusedOf kind) . fst) (homesOf kind imported names)
            homesOf kind imported names = [(slot, home) | (slot, (moduleName, fieldName)) <- zip [0 ..] names, Just home <- [homeOf kind imported world world.registered moduleName fieldName]]
            binding =
                Bound
                    { globals = homes globalExport (.globals) imports.globals
                    , memories = homes memoryExport (.memories) imports.memories
                    , tables = homes tableExport (.tables) imports.tables
                    , names = world.registered
                    }
            -- (The active segments may have written to what the module imports.)
            added = push x world {instances = IntMap.insert x (instanceOf inst) world.instances, interfaces = maybe id (IntMap.insert x) (moduleInterface m) world.interfaces, bound = IntMap.insert x binding world.bound, next = x + 1}
         in case (failed, start) of
                (Just failure, _) -> (added, Left failure, Just x)
                (Nothing, Nothing) -> (added, Right x, Just x)
                (Nothing, Just index) -> case callFunction added x index [] of
                    (started, Right _) -> (started, Right x, Just x)
                    (started, Left (Trapped trap)) -> (started, Left (StartFunctionTrapped trap), Just x)
                    (started, Left _) -> (started, Left StartFunctionNeedsHost, Just x)
  where
    x = world.next
    imports = stateImportsOf m
    -- The first import that names an object another import of the module names already. (A
    -- global that cannot be written may be imported any number of times: each index has its value.)
    twice =
        firstRepeated [(homeOf memoryExport (.memories) world world.registered moduleName fieldName, name) | (slot, name@(moduleName, fieldName)) <- zip [0 ..] imports.memories, slot `notElem` unusedOf memoryExport]
            <|> firstRepeated [(homeOf tableExport (.tables) world world.registered moduleName fieldName, name) | (slot, name@(moduleName, fieldName)) <- zip [0 ..] imports.tables, slot `notElem` unusedOf tableExport]
            <|> firstRepeated [(home, name) | (slot, name@(moduleName, fieldName)) <- zip [0 ..] imports.globals, slot `notElem` unusedOf globalExport, let home = homeOf globalExport (.globals) world world.registered moduleName fieldName, writable home]
    -- The imports of a kind that the module declares it does not use, which the elaborator has checked.
    unusedOf :: (ExportDesc -> Maybe Int) -> [Int]
    unusedOf kind = map fromIntegral $ case (kind (ExportGlobal (GlobalIdx 0)), kind (ExportMem (MemoryIdx 0))) of
        (Just _, _) -> imports.unused.globals
        (_, Just _) -> imports.unused.memories
        _ -> imports.unused.tables

    {- The first import whose type as written does not fit what it names, where both modules
       wrote types: the erased types, which instantiation compares, say nothing of whether a
       reference may be null or of which function type it is. A function must have the very
       type, a global that can be written and a table the very type of value, and a global
       that cannot be written a type of value that may go where the import's is expected. -}
    mismatched = do
        mine <- moduleInterface m
        let function name@(moduleName, fieldName) declared = do
                (y, index) <- exported functionExport world world.registered moduleName fieldName
                theirs <- IntMap.lookup y world.interfaces >>= \other -> nth other.functions index
                if theirs == declared then Nothing else Just name
            global name@(moduleName, fieldName) declared = do
                home@(y, index) <- homeOf globalExport (.globals) world world.registered moduleName fieldName
                theirs <- IntMap.lookup y world.interfaces >>= \other -> nth other.globals index
                if (if writable (Just home) then theirs == declared else closedBelow theirs declared) then Nothing else Just name
            table name@(moduleName, fieldName) declared = do
                (y, index) <- homeOf tableExport (.tables) world world.registered moduleName fieldName
                theirs <- IntMap.lookup y world.interfaces >>= \other -> nth other.tables index
                if theirs == declared then Nothing else Just name
        foldr (<|>) Nothing (zipWith function imports.functions mine.functions ++ zipWith global imports.globals mine.globals ++ zipWith table imports.tables mine.tables)
    nth xs i = case drop i xs of
        found : _ -> Just found
        [] -> Nothing
    writable home = case home >>= \(y, index) -> IntMap.lookup y world.instances >>= (`globalAt` index) of
        Just (mutability, _, _) -> mutability /= Immutable
        Nothing -> False
    firstRepeated named = case [name | (i, (Just home, name)) <- zip [0 :: Int ..] named, home `elem` [earlier | (Just earlier, _) <- take i named]] of
        name : _ -> Just name
        [] -> Nothing

{- | A decoded module in which an object imported twice is used under its first index only: for
  an import that names a memory, a table or a writable global that an earlier import of the
  module names too, every use of its index is rewritten to the earlier index, and the import is
  declared unused ('Syntax.Module.Aliases'). The two imports are one object in the world, and
  an instance cannot hold one object at two indices; after this it does not have to. To be
  applied to a module before it is validated for this world.
-}
unaliased :: World -> RawModule -> RawModule
unaliased world m =
    (renamed rename m) {aliases = Aliases (map fst globals) (map fst memories) (map fst tables)}
  where
    rename kind index = fromMaybe index . lookup index $ case kind of
        OfGlobals -> globals
        OfMemories -> memories
        OfTables -> tables
    -- Each import that names what an earlier one names, with the index of the earliest such.
    repeats homes = [(fromIntegral j, fromIntegral i) | (j, Just home) <- zip [0 :: Int ..] homes, i : _ <- [[i | (i, Just earlier) <- zip [0 :: Int ..] (take j homes), earlier == home]]]
    memories = repeats [homeOf memoryExport (.memories) world world.registered moduleName fieldName | (moduleName, fieldName) <- m.stateImports.memories]
    tables = repeats [homeOf tableExport (.tables) world world.registered moduleName fieldName | (moduleName, fieldName) <- m.stateImports.tables]
    -- (A global that cannot be written may be imported twice as it is: each index has its value.)
    globals = repeats [if writes home then home else Nothing | (moduleName, fieldName) <- m.stateImports.globals, let home = homeOf globalExport (.globals) world world.registered moduleName fieldName]
    writes home = case home >>= \(y, index) -> IntMap.lookup y world.instances >>= (`globalAt` index) of
        Just (mutability, _, _) -> mutability /= Immutable
        Nothing -> False

-- | Take what instance @x@ imports from its homes.
pull :: Int -> World -> World
pull x world = case (IntMap.lookup x world.instances, IntMap.lookup x world.bound) of
    (Just inst, Just binding) -> world {instances = IntMap.insert x (taking binding inst) world.instances}
    _ -> world
  where
    taking binding =
        over binding.globals (\slot home index inst -> maybe inst (\(_, _, value) -> putGlobalAt slot value inst) (globalAt home index))
            . over binding.memories (\slot home index inst -> maybe inst (\memory -> putMemoryAt slot memory inst) (memoryAt home index))
            . over binding.tables (\slot home index inst -> maybe inst (\given -> putTableAt slot given.table inst) (tableAt home index))
    over imported taken inst = foldr (\(slot, (home, index)) current -> maybe current (\from -> taken slot from index current) (IntMap.lookup home world.instances)) inst imported

-- | Give what instance @x@ imports back to its homes.
push :: Int -> World -> World
push x world = case (IntMap.lookup x world.instances, IntMap.lookup x world.bound) of
    (Just inst, Just binding) ->
        let giving =
                [(home, \to -> maybe to (\(_, _, value) -> putGlobalAt index value to) (globalAt inst slot)) | (slot, (home, index)) <- binding.globals]
                    ++ [(home, \to -> maybe to (\memory -> putMemoryAt index memory to) (memoryAt inst slot)) | (slot, (home, index)) <- binding.memories]
                    ++ [(home, \to -> maybe to (\given -> putTableAt index given.table to) (tableAt inst slot)) | (slot, (home, index)) <- binding.tables]
         in world {instances = foldr (\(home, give) -> IntMap.adjust give home) world.instances giving}
    _ -> world

-- | Call an exported function of an instance, with arguments in declared order.
callExport :: World -> Int -> Text -> [Value] -> (World, Either RunError [Value])
callExport world x name args = case IntMap.lookup x world.instances >>= (`exportOf` name) >>= functionExport of
    Just index -> callFunction world x (fromIntegral index) args
    Nothing -> (world, Left (NoSuchExport name))

{- | Call a function of an instance, by its index, and answer the calls it makes out of its
  module by calling the functions they name, in their instances. The world comes back as the
  call left it, also when it trapped: a trap ends every activation on the way, and undoes
  nothing. An exception that nothing caught, in any of the modules it passed through, ends the
  call like a trap.
-}
callFunction :: World -> Int -> Word32 -> [Value] -> (World, Either RunError [Value])
callFunction world x index args = case enter world x index args of
    (after, Gave results) -> (after, Right results)
    (after, Raised _) -> (after, Left (Trapped UncaughtException))
    (after, Failed failure) -> (after, Left failure)

-- | How a call of a function of an instance ended: with results, with an exception nothing in it caught, or not at all.
data Ended = Gave [Value] | Raised Escaping | Failed RunError

enter :: World -> Int -> Word32 -> [Value] -> (World, Ended)
enter world x index args = case IntMap.lookup x pulled.instances of
    Nothing -> (world, Failed (NoSuchExport "an instance by its number"))
    Just inst -> case enterFunction inst index args of
        (entered, progress) -> settle x pulled {instances = IntMap.insert x entered pulled.instances} progress
  where
    pulled = pull x world

{- | Go on from where instance @x@ stopped: it returned, trapped, threw, or calls out. A call
  out is answered by the function it names; if that one ends with an exception, the exception
  is thrown in @x@ where the call was, and a clause of @x@ may catch it.
-}
settle :: Int -> World -> Either RunError Progress -> (World, Ended)
settle x world progress = case progress of
    Left failure -> (given, Failed failure)
    Right (Returns results) -> (given, Gave results)
    Right (Throws exception) -> (given, Raised exception)
    Right (Calls call) -> case resolve x call given of
        Left failure -> (abandoned given, Failed failure)
        Right (y, index) -> case enter given y index call.arguments of
            (after, Failed failure) -> (abandoned after, Failed failure)
            (after, Gave results) -> continuing after (`resumeInstance` results)
            (after, Raised exception) -> continuing after (`throwInto` exception)
  where
    given = push x world
    abandoned current = current {instances = IntMap.adjust abandonCall x current.instances}
    continuing after continue =
        let taken = pull x after
         in case IntMap.lookup x taken.instances of
                Nothing -> (after, Failed (NoSuchExport "an instance by its number"))
                Just inst -> case continue inst of
                    (resumed, further) -> settle x taken {instances = IntMap.insert x resumed taken.instances} further

{- | The function a call out of instance @x@ goes to. One named by a reference must have the
  value types the call expects, which is the check of an indirect call that the caller could
  not make, and public results.
-}
resolve :: Int -> ForeignCall -> World -> Either RunError (Int, Word32)
resolve x call world = case call.target of
    ImportedAs moduleName fieldName -> case IntMap.lookup x world.bound >>= \binding -> exported functionExport world binding.names moduleName fieldName of
        Just (y, index) -> Right (y, fromIntegral index)
        Nothing -> Left (ForeignCallUnanswered moduleName fieldName)
    ReferencedBy reference -> case functionReferent reference of
        Nothing -> Left (Trapped UninitializedElement)
        Just (y, index) -> case IntMap.lookup (fromIntegral y) world.instances >>= (`functionType` index) of
            Nothing -> Left (Trapped UninitializedElement)
            Just (signature, resultLevels)
                | signature /= call.expected -> Left (Trapped IndirectCallTypeMismatch)
                | any (/= Low) resultLevels -> Left (Trapped InformationFlowViolation)
                | otherwise -> Right (fromIntegral y, index)
