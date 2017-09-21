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

---------------------------------------------------
-- Part II: Profunctors as Generalized Functions --
---------------------------------------------------

-- Functor

-- class Functor f where
--   fmap :: (a -> b) -> f a -> f b

-- instance Functor ((->) r) where
--   fmap f g = g . f

-- Contravariant

class Contravariant f where
  cmap :: (b -> a) -> f a -> f b

newtype CReader r a = CReader (a -> r)

instance Contravariant (CReader r) where
  cmap f (CReader g) = CReader (g . f)

-- Profunctor

class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

  lmap :: (a' -> a) -> p a b -> p a' b
  lmap f = dimap f id
  rmap :: (b -> b') -> p a b -> p a b'
  rmap f = dimap id f

instance Profunctor (->) where
  dimap f g h = g . h . f

-- Cartesian

class Profunctor p => Cartesian p where
  first  :: p a b -> p (a, c) (b, c)
  second :: p a b -> p (c, a) (c, b)

instance Cartesian (->) where
  first  f (a, c) = (f a, c)
  second f (c, a) = (c, f a)

-- Cocartesian

class Profunctor p => Cocartesian p where
  left  :: p a b -> p (Either a c) (Either b c)
  right :: p a b -> p (Either c a) (Either c b)

instance Cocartesian (->) where
  left  f = either (Left . f) Right
  right f = either Left (Right . f)

-- Monoidal

class Profunctor p => Monoidal p where
  par   :: p a b -> p c d -> p (a, c) (b, d)
  empty :: p () ()

instance Monoidal (->) where
  par f g (a, c) = (f a, g c)
  empty = id

-- Beyond Functions

newtype UpStar f a b = UpStar { runUpStar :: a -> f b }

instance Functor f => Profunctor (UpStar f) where
  dimap f g (UpStar h) = UpStar (fmap g . h . f)

instance Functor f => Cartesian (UpStar f) where
  first  (UpStar f) = UpStar (\(a, c) -> fmap (,c) (f a))
  second (UpStar f) = UpStar (\(c, a) -> fmap (c,) (f a))

instance Applicative f => Cocartesian (UpStar f) where
  left  (UpStar f) = UpStar (either (fmap Left . f) (fmap Right . pure))
  right (UpStar f) = UpStar (either (fmap Left . pure) (fmap Right . f))

instance Applicative f => Monoidal (UpStar f) where
  par (UpStar f) (UpStar g) = UpStar (\(a, b) -> (,) <$> f a <*> g b)
  empty = UpStar pure

newtype Tagged a b = Tagged { unTagged :: b }

instance Profunctor Tagged where
  dimap _ g (Tagged b) = Tagged (g b)

instance Cocartesian Tagged where
  left  (Tagged b) = Tagged (Left b)
  right (Tagged b) = Tagged (Right b)

instance Monoidal Tagged where
  par (Tagged b) (Tagged d) = Tagged (b, d)
  empty = Tagged ()
