module Any where

import Data.Kind
import GHC.TypeError

data NonEmpty :: Type where
  (:|) :: Type -> [Type] -> NonEmpty

data Any :: NonEmpty -> Type where
  Here :: a -> Any (a ':| as)
  There :: Any (b ':| as) -> Any (a ':| (b ': as))

type family (<>) (xs :: [Type]) (ys :: [Type]) :: [Type] where
  (<>) '[] ys = ys
  (<>) (x ': xs) ys = x ': xs <> ys

class Push (a :: Type) (ts :: NonEmpty) where
  push :: a -> Any ts

instance Push a (a ':| ts) where
  push = Here

instance {-# INCOHERENT #-} (Push a (t ':| ts)) => Push a (b ':| (t ': ts)) where
  push = There . push

type family ToNonEmpty (ts :: [Type]) :: NonEmpty where
  ToNonEmpty (t ': ts) = t ':| ts
  ToNonEmpty '[] = TypeError (Text "Cannot construct a NonEmpty sum type. Use a non-empty list.")

type AnyOf ts = Any (ToNonEmpty ts)
