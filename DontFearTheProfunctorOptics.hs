{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module DontFearTheProfunctorOptics where

import Data.Functor

--------------------------------
-- Part I: Optics, Concretely --
--------------------------------

-- Adapter

data Adapter s t a b = Adapter { from :: s -> a
                               , to   :: b -> t }

fromTo :: Eq s => Adapter s s a a -> s -> Bool
fromTo (Adapter f t) s = (t . f) s == s

toFrom :: Eq a => Adapter s s a a -> a -> Bool
toFrom (Adapter f t) a = (f . t) a == a

assoc :: Adapter ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
assoc = Adapter f t where
  f ((a, b), c) = (a, (b, c))
  t (a', (b', c')) = ((a', b'), c')

-- Lens

data Lens s t a b = Lens { view   :: s -> a
                         , update :: (b, s) -> t }

viewUpdate :: Eq s => Lens s s a a -> s -> Bool
viewUpdate (Lens v u) s = u ((v s), s) == s

updateView :: Eq a => Lens s s a a -> a -> s -> Bool
updateView (Lens v u) a s = v (u (a, s)) == a

updateUpdate :: Eq s => Lens s s a a -> a -> a -> s -> Bool
updateUpdate (Lens v u) a1 a2 s = u (a2, (u (a1, s))) == u (a2, s)

π1 :: Lens (a, c) (b, c) a b
π1 = Lens v u where
  v = fst
  u (b, (_, c)) = (b, c)

(|.|) :: Lens s t a b -> Lens a b c d -> Lens s t c d
(Lens v1 u1) |.| (Lens v2 u2) = Lens v u where
  v = v2 . v1
  u (d, s) = u1 ((u2 (d, (v1 s))), s)

-- Prism

data Prism s t a b = Prism { match :: s -> Either a t
                           , build :: b -> t }

matchBuild :: Eq s => Prism s s a a -> s -> Bool
matchBuild (Prism m b) s = either b id (m s) == s

buildMatch :: (Eq a, Eq s) => Prism s s a a -> a -> Bool
buildMatch (Prism m b) a = m (b a) == Left a

the :: Prism (Maybe a) (Maybe b) a b
the = Prism (maybe (Right Nothing) Left) Just

-- Affine

data Affine s t a b = Affine { preview :: s -> Either a t
                             , set     :: (b, s) -> t }

previewSet :: Eq s => Affine s s a a -> s -> Bool
previewSet (Affine p st) s = either (\a -> st (a, s)) id (p s) == s

setPreview :: (Eq a, Eq s) => Affine s s a a -> a -> s -> Bool
setPreview (Affine p st) a s = p (st (a, s)) == either (Left . const a) Right (p s)

setSet :: Eq s => Affine s s a a -> a -> a -> s -> Bool
setSet (Affine p st) a1 a2 s = st (a2, (st (a1, s))) == st (a2, s)

maybeFirst :: Affine (Maybe a, c) (Maybe b, c) a b
maybeFirst = Affine p st where
  p (ma, c) = maybe (Right (Nothing, c)) Left ma
  st (b, (ma, c)) = (ma $> b, c)

-- Traversal

data Traversal s t a b = Traversal { contents :: s -> [a]
                                   , fill     :: ([b], s) -> t }

firstNSecond :: Traversal (a, a, c) (b, b, c) a b
firstNSecond = Traversal c f where
  c (a1, a2, _)  = [a1, a2]
  f (bs, (_, _, x)) = (head bs, (head . tail) bs, x)

-- Right Traversal

data FunList a b t = Done t | More a (FunList a b (b -> t))

newtype Traversal' s t a b = Traversal' { extract :: s -> FunList a b t }

firstNSecond' :: Traversal' (a, a, c) (b, b, c) a b
firstNSecond' = Traversal' (\(a1, a2, c) -> More a1 (More a2 (Done (,,c))))
