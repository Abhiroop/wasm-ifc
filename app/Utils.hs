{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PatternSynonyms #-}

module Utils where
import Data.Type.Equality ((:~:)(Refl))
import Data.Kind

-----------------------------------------------------------------------------
-- PEANO NATS
-----------------------------------------------------------------------------

data Nat = Z | S Nat

type family (:==) (a :: Nat) (b :: Nat) :: Bool where
    'Z :== 'Z = 'True
    'Z :== ('S b) = 'False
    ('S a) :== 'Z = 'False
    ('S a) :== ('S b) = a :== b

data SNat (n :: Nat) where
    SZ :: SNat 'Z
    SS :: SNat n -> SNat ('S n)

type family LogicalAnd (a :: Bool) (b :: Bool) :: Bool where
    LogicalAnd 'True 'True = 'True
    LogicalAnd _ _ = 'False

type family LessThan (i :: Nat) (j :: Nat) :: Bool where
    LessThan 'Z ('S j)       = 'True
    LessThan _ 'Z       = 'False -- So it also returns False if i == j
    LessThan ('S i) ('S j)   = LessThan i j

type family LessEqThan (i :: Nat) (j :: Nat) :: Bool where
    LessEqThan 'Z j           = 'True
    LessEqThan ('S i) 'Z      = 'False
    LessEqThan ('S i) ('S j)  = LessEqThan i j

type family IsEqual (i :: Nat) (j :: Nat) :: Bool where
    IsEqual 'Z 'Z             = 'True
    IsEqual 'Z ('S j)        = 'False
    IsEqual ('S i) 'Z        = 'False
    IsEqual ('S i) ('S j)    = IsEqual i j

-- type level Peano Nat Equality check
pEqual :: Nat -> Nat -> Bool
pEqual Z Z = True
pEqual Z (S _) = False
pEqual (S _) Z = False
pEqual (S m) (S n) = pEqual m n


-- Peano Nat subtraction
infixr 5 :-
type family (m :: Nat) :- (n :: Nat) :: Nat where
    m :- 'Z         = m
    ('S m) :- ('S n) = m :- n


-- Peano Nat addition
type family (m :: Nat) +: (n :: Nat) :: Nat where
    'Z +: n         = n
    'S m +: n = 'S (m +: n)
type family (m :: Nat) :+ (n :: Nat) :: Nat where
    m :+ 'Z         = m
    m :+ 'S n = 'S (m :+ n)

-- term level addition and subtraction
addPNats :: Nat -> Nat -> Nat
addPNats a Z = a
addPNats a (S m) = S (addPNats a m)

subPNats :: Nat -> Nat -> Nat
subPNats a Z = a
subPNats (S m) (S n) = subPNats m n
subPNats Z (S _) = error "subPNats: negative result"

-- (.+.) :: SNat a -> SNat b -> SNat (a :+ b)
-- SZ .+. b    = b
-- SS m .+. b = SS (m .+. b)
-- type family (m :: Nat) ::+ (n :: Nat) :: Nat where
--     'Z ::+ n        = n
--     m ::+ ('S n) = 'S (m ::+ n)


-----------------------------------------------------------------------------
-- TYPE-LEVEL VECTORS
-----------------------------------------------------------------------------

data Vec (n :: Nat) a where
    VNil  :: Vec 'Z a
    (:<|) :: a -> Vec n a -> Vec ('S n) a
infixr 5 :<|




-- | Type-level indexing into vectors
type family Index (i :: Nat) (v :: [a]) :: a where
    Index 'Z (x : _)      =  x
    Index ('S n) (_ ': xs) = Index n xs

-- | Type-level function to get the length of a vector
-- type family GetVecLen (v :: [a]) :: Nat where
--     GetVecLen (v :: [a]) = n

    


-----------------------------------------------------------------------------
-- Type Level Finite Indices
-----------------------------------------------------------------------------

{-@ This is slightly different from the Fin n type
    that we had. Here we have an additional type
    parameter tracking the current index (i) and
    the bound of the vector (n)
    The `i` parameter is a WITNESS to the specific index value
@-}
data SFin (i :: Nat) (n :: Nat) where
    SFZ :: 
        -- (LessThan 'Z ('S n) ~ 'True) => 
        SFin 'Z ('S n)
    SFS :: 
        -- (LessThan i ('S n) ~ 'True) => 
        SFin i n -> SFin ('S i) ('S n)

sexample1 :: SFin 'Z ('S ('S 'Z))        -- Specifically index 0, for length 2
sexample1 = SFZ

sexample2 :: SFin ('S 'Z) ('S ('S 'Z))   -- Specifically index 1, for length 2
sexample2 = SFS SFZ


--------------------------------------------------------------------------------
-- Generic heterogeneous list parameterised by an "eval" function:
--   eval :: k -> Type
-- HListF eval '[x1,x2,...] stores values of types (eval x1), (eval x2), ...
--------------------------------------------------------------------------------

data HListF (eval :: k -> Type) (xs :: [k]) where
  HNilF :: HListF eval '[]
  (:#)  :: eval x -> HListF eval xs -> HListF eval (x ': xs)

infixr 5 :#