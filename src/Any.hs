{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}

module Any where

import Data.Kind (Type)
import GHC.TypeLits (ErrorMessage(..), TypeError)
import Data.Data (Proxy (..))

-------------
-- OPEN SUM
-------------

data Any :: [Type] -> Type where
  Here  :: a       -> Any (a ': as)
  There :: Any as  -> Any (b ': as)

-------------------
-- SUM MEMBERSHIP
-------------------

-- | Membership evidence that 'a' occurs in 'ts'.
data Member :: k -> [k] -> Type where
  Head ::                Member a (a ': as) -- at the head
  Tail :: Member a as -> Member a (b ': as) -- in the tail

data N = Z | S N

-- | Find the (leftmost) position of 'a' in 'ts' as a Peano index.
type family Find (a :: k) (ts :: [k]) :: N where
  Find a '[]       = TypeError ('Text "Type " ':<>: 'ShowType a ':<>: 'Text " is not a member of the list")
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

------------------
-- SUM INJECTION
------------------

injectAt :: Member a ts -> a -> Any ts
injectAt Head     x = Here x
injectAt (Tail i) x = There $ injectAt i x

inject :: forall a ts. BuildMember (Find a ts) a ts => a -> Any ts
inject = injectAt (member @a @ts)

-------------------
-- SUM PROJECTION
-------------------

projectFrom :: Member a ts -> Any ts -> Maybe a
projectFrom Head       (Here x)  = Just x
projectFrom Head       (There _) = Nothing
projectFrom (Tail _)   (Here _)  = Nothing
projectFrom (Tail prf) (There v) = projectFrom prf v

project :: forall a ts. BuildMember (Find a ts) a ts => Any ts -> Maybe a
project = projectFrom (member @a @ts)

----------------
-- ELIMINATION
----------------

-- Case on the head of a sum:
caseAny :: (a -> r) -> (Any as -> r) -> Any (a ': as) -> r
caseAny f _ (Here x)  = f x
caseAny _ g (There v) = g v

none :: Any '[] -> a
none empty = case empty of {}

infixr 5 :&
data Cotuple (r :: Type) (as :: [Type]) :: Type where
  Nil  ::                             Cotuple r '[]
  (:&) :: (a -> r) -> Cotuple r as -> Cotuple r (a ': as)

cotuple :: Cotuple r as -> Any as -> r
cotuple (f :& _)  (Here x)  = f x
cotuple (_ :& fs) (There v) = cotuple fs v
cotuple Nil       v         = none v

(<+>) :: Cotuple a as -> Cotuple a bs -> Cotuple a (as <> bs)
(<+>) Nil       gs = gs
(<+>) (f :& fs) gs = f :& fs <+> gs

---------------
-- TYPE UTILS
---------------

type family (<>) (xs :: [k]) (ys :: [k]) :: [k] where
  (<>) '[]       ys = ys
  (<>) (x ': xs) ys = x ': xs <> ys

type family (<|>) u v where
  (<|>) (Any xs)       (Any ys)       = Any (xs <> ys)
  (<|>) (Cotuple r fs) (Cotuple r gs) = Cotuple r (fs <> gs)

type family Remove (a :: Type) (ts :: [Type]) :: [Type] where
  Remove _ '[]       = '[]
  Remove a (a ': as) = Remove a as
  Remove a (b ': as) = b : Remove a as

type family Elim a u where
  Elim a (Any ts)       = Any (Remove a ts)
  Elim a (Cotuple r ts) = Cotuple r (Remove a ts)

type family (\\) (xs :: [Type]) (ys :: [Type]) :: [Type] where
  xs \\ '[]       = xs
  xs \\ (y ': ys) = Remove y xs \\ ys

type family Diff u v where
  Diff (Any as)       (Any bs)       = Any (as \\ bs)
  Diff (Cotuple r as) (Cotuple r bs) = Cotuple r (as \\ bs)

-- Convert from an ADT to open sum
class ToAny a as where
  toAny :: a -> Any as

-- Convert from an open sum to an ADT
class FromAny a as where
  fromAny :: Any as -> a

instance ToAny (Either a b) '[a, b] where
  toAny = either Here (There . Here)

instance FromAny (Either a b) '[a, b] where
  fromAny = cotuple $ Left :& Right :& Nil

instance ToAny (Maybe a) '[a, ()] where
  toAny = maybe (There $ Here ()) inject

instance FromAny (Maybe a) '[(), a] where
  fromAny = cotuple $ const Nothing :& Just :& Nil

-------------
-- EXAMPLES
-------------

data A = A
data B = B
data C = C
data D = D

type U = '[A, B]
type V = '[C, D]

type SumU = Any U
type SumV = Any V

foo :: Any (U <> V) -> String
foo =
  caseAny (\A -> "A") $
  caseAny (\B -> "B")
  baz

foo' :: Any (U <> V) -> String
foo' = cotuple $ co <+> co'
  where
    co :: Cotuple String U
    co = const "A" :& const "B" :& Nil

    co' :: Cotuple String V
    co' = const "A" :& const "B" :& Nil

bar :: Any U -> String
bar =
  caseAny (\A -> "A") $
  caseAny (\B -> "B")
  none

baz :: SumV -> String
baz =
  caseAny (\C -> "C") $
  caseAny (\D -> "D")
  none

-- | Partially pattern match. Handle as many cases as you want.
gib :: Any (U <> V) -> Either (Any V) String
gib (Here A) = Right "A"
gib (There (Here B)) = Right "B"
gib (There (There v)) = Left v

-- | Complete pattern match. 
-- Match all, and end with a `none v` to eliminate the empty sum.
ajj :: Any U -> String
ajj (Here A)          = "A"
ajj (There (Here B))  = "B"
ajj (There (There v)) = none v

-- Eliminate certain elements from a sum.
-- Here we take Any '[A, B, C, D] into Any '[A, C], eliminating B and D.
aef :: Any (U <> V) -> Either (Any (U <> V) `Diff` Any '[B, D]) String
aef (Here A)                          = Left $ inject A
aef (There (Here B))                  = Right "B"
aef (There (There (Here C)))          = Left $ inject C
aef (There (There (There (Here D))))  = Right "D"
aef (There (There (There (There v)))) = none v

boef :: Any (U <> V) -> Either (Elim A (Any (U <> V))) String
boef  (Here A)                          = Right "A"
boef  (There (Here B))                  = Left $ inject B
boef  (There (There (Here C)))          = Left $ inject C
boef  (There (There (There (Here D))))  = Left $ inject D
boef  (There (There (There (There v)))) = none v

