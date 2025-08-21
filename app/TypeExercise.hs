{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module TypeExercise where

import Prelude hiding (head, replicate, (++), Double)

-- 1) type-level natural numbers
data Nat = Z | S Nat

-- 2) singletons for Nat (value witness for types)
data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- optional helper to build small SNats
s0 :: SNat 'Z
s0 = SZ
s1 :: SNat ('S 'Z)
s1 = SS SZ
s2 :: SNat ('S ('S 'Z))
s2 = SS s1

-- 3) length-indexed vector as a GADT
data Vec (n :: Nat) a where
  VNil  :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a

infixr 5 `VCons`

-- IMP: First usage of type families
-- 4) type family for addition on Nats
type family Add (m :: Nat) (n :: Nat) :: Nat where
  Add 'Z     n = n
  Add ('S m) n = 'S (Add m n)

-- 5) append vectors: lengths add at the type level
(++) :: Vec m a -> Vec n a -> Vec (Add m n) a
VNil      ++ ys = ys
VCons x xs ++ ys = VCons x (xs ++ ys)

{-@ Exercise 1
    Implement

    type family Double (n :: Nat) :: Nat where
       -- implement

    and now implement

    duplicate :: Vec n a -> Vec (Double n) a
    duplicate = undefined

    such that duplicate [x1,x2,x3] gives [x1,x1,x2,x2,x3,x3]

@-}


{-@ Exercise 2
    Implement `head`

    For normal lists we have

    head :: [a] -> a

    What would the type of `head` for `Vec n a`
    Think and give the type and implementation.
@-}



-- 7) zipWith for vectors of the same length
zipWithVec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithVec _ VNil VNil = VNil
zipWithVec f (VCons x xs) (VCons y ys) = VCons (f x y) (zipWithVec f xs ys)


{-@ Exercise 3
    Implement `replicate`

    For normal lists we have

    replicate :: Int -> a -> [a]
    replicate 0 a = []
    replicate n a = a : (replicate (n - 1) a)

    What would the type of `replicate` be for `Vec n a`
    Think and give the type and implementation.
@-}


{-@ Exercise 4
    Implement `takeVec`, `dropVec`

    Take your time and implement these. Once again note

    take :: Int -> [a] -> [a]
    drop :: Int -> [a] -> [a]

    For length indexed vectors, we have to come up with
    our own type families. Take your time, think of the types
    and implement this. Should give good insight into
    general type-level programming and debugging type errors.
@-}

{-@ Exercise 5
    Implement `index`
@-}

-- 9) Fin index type and safe indexing
data Fin (n :: Nat) where
  FZ :: Fin ('S n)         -- zero index, valid in any 'S n
  FS :: Fin n -> Fin ('S n)

index :: Fin n -> Vec n a -> a
index = undefined
-- note: indexing into VNil is impossible by the types

-- example values
v1 :: Vec ('S ('S 'Z)) Int
v1 = VCons 10 (VCons 20 VNil)

v2 :: Vec ('S ('S ('S 'Z))) Int
v2 = VCons 1 (VCons 2 (VCons 3 VNil))

v3 :: Vec ('S ('S ('S 'Z))) Int
v3 = VCons 10 (VCons 20 (VCons 30 VNil))


i0 :: Fin ('S ('S ('S 'Z)))
i0 = FZ          -- index 0

i1 :: Fin ('S ('S ('S 'Z)))
i1 = FS FZ       -- index 1

i2 :: Fin ('S ('S ('S 'Z)))
i2 = FS (FS FZ)  -- index 2

-- if implemented correctly, we should have
-- index i0 v3 == 10
-- index i1 v3 == 20
-- index i2 v3 == 30

{-@ Exercise 6 : Proofs!
    Prove Add n 'Z == n

    Intuitively, of course its true.
    But what is `==`? Is there some type-level
    notion of equality in Haskell? Read and find more!

    You might have to import libraries and add language
    extensions for this.

@-}


{-@ Exercise 7 : More Proofs!
    Prove Vec n a ++ VNil == Vec n a

    This is the toughest exercise.
    This might be tricky, so don't expect
    the full solution right away. This uses
    an exotic function at the corners of
    type equality in Haskell.

    Its main purpose is to illustrate that the
    type system of Haskell is expressive enough to
    approach things that proof assistants do.

@-}
