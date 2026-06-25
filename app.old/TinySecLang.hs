{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module TinySecLang where

import Data.Kind (Type)
import GHC.TypeLits (Symbol)

-- ## Security Levels
-- Define security levels as a kind with a lattice: Public < Secret
data SecLevel = Public | Secret

data SSecLevel (l :: SecLevel) where
  SPublic :: SSecLevel 'Public
  SSecret :: SSecLevel 'Secret

reflect :: SSecLevel l -> SecLevel
reflect SPublic = Public
reflect SSecret = Secret

-- ## Type Family for Joining Security Levels
-- Defines the lattice join operation: Public ⊔ Public = Public, otherwise Secret
type family Join (l1 :: SecLevel) (l2 :: SecLevel) :: SecLevel where
  Join 'Public 'Public = 'Public
  Join _ _ = 'Secret

-- Runtime join function;
-- XXX: A dynamic approach would use this in label raising operations of evalExpr
-- like if
-- join :: SSecLevel l1 -> SSecLevel l2 -> SSecLevel (Join l1 l2)
-- join SPublic SPublic = SPublic
-- join SPublic SSecret = SSecret
-- join SSecret SPublic = SSecret
-- join SSecret SSecret = SSecret


-- ## Type Class for Security Level Ordering
-- Enforces the lattice ordering: Public ≤ Public, Public ≤ Secret, Secret ≤ Secret
class LE (l :: SecLevel) (l' :: SecLevel)
instance LE 'Public 'Public
instance LE 'Public 'Secret
instance LE 'Secret 'Secret

-- ## Store Definition
-- A simple key-value store mapping variable names to integers
type Store = [(String, Int)]

-- Lookup a variable in the store, defaulting to 0 if not found
lookupStore :: Store -> String -> Int
lookupStore store x = maybe 0 id (lookup x store)

-- Update a variable in the store
updateStore :: Store -> String -> Int -> Store
updateStore store x v = (x, v) : filter (\(y, _) -> y /= x) store

-- ## Secure Expressions
-- Expressions indexed by their security level
data SecExpr (l :: SecLevel) where
  SLit  :: Int -> SecExpr 'Public              -- Literals are always Public
  SVar  :: String -> SSecLevel l -> SecExpr l  -- Variables carry their security level
  SBinOp :: SecExpr l1 -> SecExpr l2 -> SecExpr (Join l1 l2)  -- Addition joins levels
  SEq   :: SecExpr l1 -> SecExpr l2 -> SecExpr (Join l1 l2)   -- Equality joins levels

-- ## Secure Statements
-- Statements indexed by the program counter's security level (pc)
data SecureStmt (pc :: SecLevel) where
  SAssign :: LE (Join l pc) lx => String -> SSecLevel lx -> SecExpr l -> SecureStmt pc
  SIf     :: SecExpr l -> [SecureStmt (Join pc l)] -> [SecureStmt (Join pc l)] -> SecureStmt pc

-- ## Program Type
-- A coherent type encapsulating a list of statements with a specific pc level
data Program (pc :: SecLevel) where
  Program :: [SecureStmt pc] -> Program pc

-- Type alias for programs starting in a Public context
type PublicProgram = Program 'Public

-- ## Expression Evaluation
-- Evaluates a secure expression given a store
evalExpr :: Store -> SecExpr l -> Int
evalExpr _ (SLit n) = n
evalExpr store (SVar x _) = lookupStore store x
evalExpr store (SBinOp e1 e2) = evalExpr store e1 + evalExpr store e2
evalExpr store (SEq e1 e2) = if evalExpr store e1 == evalExpr store e2 then 1 else 0

-- ## Statement Execution
-- Executes a single statement, updating the store
execStmt :: Store -> SecureStmt pc -> Store
execStmt store (SAssign x _ e) = updateStore store x (evalExpr store e)
execStmt store (SIf e thenStmts elseStmts) =
  let v = evalExpr store e
      branch = if v /= 0 then thenStmts else elseStmts
  in foldl execStmt store branch

-- ## Execute a List of Statements
-- Folds over a list of statements to update the store
execStmts :: Store -> [SecureStmt pc] -> Store
execStmts = foldl execStmt

-- ## Program Interpreter
-- Interprets an entire program starting from an initial store
interpret :: Store -> Program pc -> Store
interpret store (Program stmts) = execStmts store stmts

-- ## Initial Store
initialStore :: Store
initialStore = [("x", 0), ("y", 1), ("z", 0)]

-- ## Example Program 1: Public Guard Updates Secret Variable
secureProg1 :: PublicProgram
secureProg1 = Program
  [ SIf (SVar "x" SPublic)
        [SAssign "y" SSecret (SLit 1)]
        [SAssign "y" SSecret (SLit 2)]
  ]

-- ## Example Program 2: Secret Guard Updates Secret Variable
secureProg2 :: PublicProgram
secureProg2 = Program
  [ SIf (SVar "y" SSecret)
        [SAssign "z" SSecret (SLit 1)]
        [SAssign "z" SSecret (SLit 2)]
  ]

-- ## Example of an Insecure Program (Commented Out)
-- This would fail to compile due to security violation
-- insecureProg :: PublicProgram
-- insecureProg = Program
--   [ SIf (SVar "y" SSecret)
--         [SAssign "x" SPublic (SLit 1)]
--         [SAssign "x" SPublic (SLit 2)]
--   ]
-- Error: No instance for (LE 'Secret 'Public)


main :: IO ()
main = do
  let finalStore1 = interpret initialStore secureProg1
      finalStore2 = interpret initialStore secureProg2
  putStrLn $ "SecureProg1 final store: " ++ show finalStore1
  putStrLn $ "SecureProg2 final store: " ++ show finalStore2
