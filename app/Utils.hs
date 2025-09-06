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

