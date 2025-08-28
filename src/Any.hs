module Any where

import Data.Kind

data Any :: [Type] -> Type where
  Here :: a -> Any (a ': as)
  There :: Any as -> Any (a ': as)

type family (<>) (xs :: [Type]) (ys :: [Type]) :: [Type] where
  (<>) '[] ys = ys
  (<>) (x ': xs) ys = x ': xs <> ys

class Push (a :: Type) (ts :: [Type]) where
  push :: a -> Any ts

instance Push a (a ': ts) where
  push = Here

instance {-# OVERLAPPABLE #-} (Push a ts) => Push a (b ': ts) where
  push = There . push
