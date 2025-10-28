{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Utils where



data SNat = Z | S SNat

data Vec (n :: SNat) a where
    VNil  :: Vec 'Z a
    (:<|) :: a -> Vec n a -> Vec ('S n) a

infixr 5 :<|


-- | Type-level indexing into vectors
type family Index (i :: SNat) (v :: Vec n a) :: a where
    Index 'Z (x :<| _)      =  x
    Index ('S n) (_ :<| xs) = Index n xs

-- type family GetVecLen (v :: Vec n a) :: SNat where
--     GetVecLen (v :: Vec n a) = n
type family GetVecLen (v :: Vec n a) :: SNat where
    GetVecLen VNil         = 'Z
    GetVecLen ( _ :<| xs)  = 'S (GetVecLen xs)


{-@ This is slightly different from the Fin n type
    that we had. Here we have an additional type
    parameter tracking the current index (i) and
    the bound of the vector (n)
    The `i` parameter is a WITNESS  to the specific index value
@-}
data SFin (i :: SNat) (n :: SNat) where
    SFZ :: SFin 'Z ('S n)
    SFS :: SFin i n -> SFin ('S i) ('S n)

sexample1 :: SFin 'Z ('S ('S 'Z))        -- Specifically index 0, for length 2
sexample1 = SFZ

sexample2 :: SFin ('S 'Z) ('S ('S 'Z))   -- Specifically index 1, for length 2
sexample2 = SFS SFZ

type family LessThan (i :: SNat) (j :: SNat) :: Bool where
    LessThan 'Z ('S j)       = 'True
    LessThan _ 'Z       = 'False -- So it also returns False if i == j
    LessThan ('S i) ('S j)   = LessThan i j

type family IsEqual (i :: SNat) (j :: SNat) :: Bool where
    IsEqual 'Z 'Z             = 'True
    IsEqual 'Z ('S j)        = 'False
    IsEqual ('S i) 'Z        = 'False
    IsEqual ('S i) ('S j)    = IsEqual i j

infixr 5 :-

type family (m :: SNat) :- (n :: SNat) :: SNat where
    m :- 'Z         = m
    ('S m) :- ('S n) = m :- n

infixl 6 :+
type family (m :: SNat) :+ (n :: SNat) :: SNat where
    'Z :+ n         = n
    ('S m) :+ n = 'S (m :+ n)



