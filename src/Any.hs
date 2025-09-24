{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Any where

import Data.Kind (Type)
import GHC.TypeLits (ErrorMessage(..), TypeError)
import Data.Data (Proxy (..))

data Any :: [Type] -> Type where
  Here  :: a       -> Any (a ': as)
  There :: Any as  -> Any (b ': as)

-- | Membership evidence that 'a' occurs in 'ts'.
data Member :: k -> [k] -> Type where
  Head ::                Member a (a ': as) -- at the head
  Tail :: Member a as -> Member a (b ': as) -- in the tail

injectAt :: Member a ts -> a -> Any ts
injectAt Head     x = Here x
injectAt (Tail i) x = There $ injectAt i x

projectAt :: Member a ts -> Any ts -> Maybe a
projectAt Head       (Here x)  = Just x
projectAt Head       (There _) = Nothing
projectAt (Tail _)   (Here _)  = Nothing
projectAt (Tail prf) (There v) = projectAt prf v

data N = Z | S N

-- | Find the (leftmost) position of 'a' in 'ts' as a Peano index.
type family Find (a :: k) (ts :: [k]) :: N where
  Find a '[]       = TypeError ( 'Text "Type " ':<>: 'ShowType a ':<>: 'Text " is not a member of the list" )
  Find a (a ': ts) = 'Z
  Find a (_ ': ts) = 'S (Find a ts)

-- | Reify the Peano index into a 'Member' witness.
class BuildMember (n :: N) (a :: k) (ts :: [k]) where
  buildMember :: Proxy n -> Member a ts

-- | Membership at the head
instance BuildMember 'Z a (a ': ts) where
  buildMember _ = Head

-- | Membership somewhere in the tail
instance BuildMember n a ts => BuildMember ('S n) a (b ': ts) where
  buildMember _ = Tail (buildMember (Proxy @n))

-- | Compute membership index
member :: forall a ts. BuildMember (Find a ts) a ts => Member a ts
member = buildMember (Proxy @(Find a ts))

inject :: forall a ts. BuildMember (Find a ts) a ts => a -> Any ts
inject = injectAt (member @a @ts)

project :: forall a ts. BuildMember (Find a ts) a ts => Any ts -> Maybe a
project = projectAt (member @a @ts)

----------------------------------------------------------------
-- Example
----------------------------------------------------------------


-- Case on the head of a sum:
caseAny :: (a -> r) -> (Any as -> r) -> Any (a ': as) -> r
caseAny f _ (Here x)  = f x
caseAny _ g (There v) = g v

absurdAny :: Any '[] -> a
absurdAny empty = case empty of {}

type family (<>) (xs :: [k]) (ys :: [k]) :: [k] where
  (<>) '[]       ys = ys
  (<>) (x ': xs) ys = x ': xs <> ys

type Union :: Type -> Type -> Type
type family Union u v where
  Union (Any xs) (Any ys) = Any (xs <> ys)

weakenLeft :: forall xs ys. Any xs -> Any (xs <> ys)
weakenLeft = go
  where
    go :: forall xs'. Any xs' -> Any (xs' <> ys)
    go (Here x)  = Here x
    go (There v) = There (go v)

-- | This allows us to do At-matching, but we don't get completeness checking
pattern At :: forall a ts. BuildMember (Find a ts) a ts => a -> Any ts
pattern At x <- (project @a -> Just x) where
  At x = inject @a x

data A = A
data B = B
data C = C
data D = D

type U = Any '[A, B]
type Y = Any '[C, D]

type W = Union U Y

foo :: W -> String
foo =
  caseAny (\A -> "A") $
  caseAny (\B -> "B")
  baz

bar :: U -> String
bar =
  caseAny (\A -> "A") $
  caseAny (\B -> "B")
  absurdAny

baz :: Y -> String
baz =
  caseAny (\C -> "C") $
  caseAny (\D -> "D")
  absurdAny

-- | Very neat pattern matching, no completeness check though
-- handleU' :: U -> String
-- handleU' (At A) = "A"
-- handleU' (At B) = "A"
-- handleU' (At C) = "A"
