-- | An import as decoded: where it comes from and what it must be.
module Syntax.Imports (
    RawImport (..),
    ImportDesc (..),
) where

import Data.Text (Text)

import Syntax.Types (FuncType)

data RawImport = RawImport
    { importModule :: Text
    , importName :: Text
    , importDesc :: ImportDesc
    }
    deriving stock (Eq, Show)

-- | What is imported. Only functions so far; their type index is resolved by the decoder.
newtype ImportDesc = ImportFunc FuncType
    deriving stock (Eq, Show)
