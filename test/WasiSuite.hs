{- | The official WASI testsuite (@WebAssembly/wasi-testsuite@), run through the CLI: every
  Preview 1 program under @tests/<language>/testsuite/wasm32-wasip1@ is executed with
  @wasm-ifc run@, with the arguments, environment and preopened root directory its JSON
  configuration asks for, and its exit code, standard output and standard error are checked
  against it. The root directory is copied for each run, since programs write into it.

  The suite is a git submodule under @test/wasi/testsuite@, pinned to a commit.
-}
module Main (main) where

import Control.Monad (forM_)
import Data.Aeson (FromJSON (..), withObject, (.!=), (.:?))
import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy qualified as BL
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (
    copyFile,
    createDirectoryIfMissing,
    createFileLink,
    doesDirectoryExist,
    doesFileExist,
    findExecutable,
    getSymbolicLinkTarget,
    getTemporaryDirectory,
    listDirectory,
    pathIsSymbolicLink,
    removePathForcibly,
 )
import System.Exit (ExitCode (..))
import System.FilePath (takeBaseName, takeExtension, (</>))
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import Test.Hspec

suiteDir :: FilePath
suiteDir = "test/wasi/testsuite/tests"

languages :: [String]
languages = ["assemblyscript", "c", "rust"]

{- | Tests we know we cannot meet, with the reason; reported as pending rather than failed so
  that any other regression still shows.
-}
knownGaps :: Map.Map String String
knownGaps = Map.empty

main :: IO ()
main = hspec $ do
    runner <- runIO (findExecutable "wasm-ifc")
    checkedOut <- runIO (doesDirectoryExist suiteDir)
    forM_ languages $ \language -> do
        let dir = suiteDir </> language </> "testsuite" </> "wasm32-wasip1"
        present <- runIO (if checkedOut then doesDirectoryExist dir else pure False)
        programs <- runIO (if present then sort . filter ((== ".wasm") . takeExtension) <$> listDirectory dir else pure [])
        describe ("wasi-testsuite: " ++ language) $
            forM_ programs $ \program -> it (takeBaseName program) $ case runner of
                Nothing -> pendingWith "the wasm-ifc executable is not on the PATH"
                Just bin
                    | not checkedOut -> pendingWith "test/wasi/testsuite is not checked out (git submodule update --init)"
                    | otherwise -> case Map.lookup (takeBaseName program) knownGaps of
                        Just reason -> pendingWith ("known gap: " ++ reason)
                        Nothing -> runTest bin dir program

-- | A test's configuration (every field optional; the defaults are the runner's).
data Config = Config
    { args :: [Text]
    , env :: Map.Map Text Text
    , root :: Maybe FilePath
    , exitCode :: Int
    , stdoutExpected :: Maybe Text
    , stderrExpected :: Maybe Text
    }

instance FromJSON Config where
    parseJSON = withObject "config" $ \o ->
        Config
            <$> o .:? "args" .!= []
            <*> o .:? "env" .!= Map.empty
            <*> o .:? "root"
            <*> o .:? "exit_code" .!= 0
            <*> o .:? "stdout"
            <*> o .:? "stderr"

defaultConfig :: Config
defaultConfig = Config [] Map.empty Nothing 0 Nothing Nothing

runTest :: FilePath -> FilePath -> FilePath -> Expectation
runTest bin dir program = do
    let configPath = dir </> takeBaseName program ++ ".json"
    hasConfig <- doesFileExist configPath
    config <-
        if hasConfig
            then either fail pure . Aeson.eitherDecode =<< BL.readFile configPath
            else pure defaultConfig
    scratch <- (</> ("wasm-ifc-wasi" </> takeBaseName program)) <$> getTemporaryDirectory
    removePathForcibly scratch
    createDirectoryIfMissing True scratch
    dirOptions <- case config.root of
        Nothing -> pure []
        Just rootDir -> do
            copyTree (dir </> rootDir) (scratch </> "root")
            pure ["--dir", (scratch </> "root") ++ "::/"]
    let envOptions = concat [["--env", T.unpack k ++ "=" ++ T.unpack v] | (k, v) <- Map.toList config.env]
        argv = dirOptions ++ envOptions ++ [program] ++ map T.unpack config.args
    (code, out, err) <- readCreateProcessWithExitCode (proc bin ("run" : argv)) {cwd = Just dir} ""
    let actualCode = case code of
            ExitSuccess -> 0
            ExitFailure n -> n
        problems =
            [ "exit code " ++ show actualCode ++ ", expected " ++ show config.exitCode ++ (if null err then "" else " (stderr: " ++ take 300 err ++ ")")
            | actualCode /= config.exitCode
            ]
                ++ ["stdout " ++ show out ++ ", expected " ++ show expected | Just expected <- [config.stdoutExpected], T.pack out /= expected]
                ++ ["stderr " ++ show err ++ ", expected " ++ show expected | Just expected <- [config.stderrExpected], T.pack err /= expected]
    case problems of
        [] -> pure ()
        _ -> expectationFailure (unlines problems)

-- | Copy a directory tree, keeping symbolic links as links (the tests probe them).
copyTree :: FilePath -> FilePath -> IO ()
copyTree from to = do
    createDirectoryIfMissing True to
    entries <- listDirectory from
    forM_ entries $ \name -> do
        let source = from </> name
            target = to </> name
        link <- pathIsSymbolicLink source
        if link
            then getSymbolicLinkTarget source >>= \destination -> createFileLink destination target
            else do
                isDir <- doesDirectoryExist source
                if isDir then copyTree source target else copyFile source target
