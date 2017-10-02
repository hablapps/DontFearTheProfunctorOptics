{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module DontFearTheProfunctorOptics where

import Data.Functor
import Data.Functor.Constant
import Data.List

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

shift :: Adapter ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
shift = Adapter f t where
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

pi1 :: Lens (a, c) (b, c) a b
pi1 = Lens v u where
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
the = Prism m b where
  m = maybe (Right Nothing) Left
  b = Just

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

firstNSecond'' :: Traversal' (a, a, c) (b, b, c) a b
firstNSecond'' = Traversal' (\(a1, a2, c) -> More a1 (More a2 (Done (,,c))))

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

---------------------------------
-- Part III: Profunctor Optics --
---------------------------------

type Optic p s t a b = p a b -> p s t

-- Profunctor Adapter

type AdapterP s t a b = forall p . Profunctor p => Optic p s t a b

adapterC2P :: Adapter s t a b -> AdapterP s t a b
adapterC2P (Adapter f t) = dimap f t

from' :: AdapterP s t a b -> s -> a
from' ad = getConstant . runUpStar (ad (UpStar Constant))

to' :: AdapterP s t a b -> b -> t
to' ad = unTagged . ad . Tagged

shift' :: AdapterP ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
shift' = dimap assoc assoc' where
  assoc  ((x, y), z) = (x, (y, z))
  assoc' (x, (y, z)) = ((x, y), z)

-- Profunctor Lens

type LensP s t a b = forall p . Cartesian p => Optic p s t a b

lensC2P :: Lens s t a b -> LensP s t a b
lensC2P (Lens v u) = dimap dup u . first . lmap v where
  dup a = (a, a)

view' :: LensP s t a b -> s -> a
view' ln = getConstant . runUpStar (ln (UpStar Constant))

update' :: LensP s t a b -> (b, s) -> t
update' ln (b, s) = ln (const b) s

pi1' :: LensP (a, c) (b, c) a b
pi1' = first

-- Profunctor Prism

type PrismP s t a b = forall p . Cocartesian p => Optic p s t a b

prismC2P :: Prism s t a b -> PrismP s t a b
prismC2P (Prism m b) = dimap m (either id id) . left . rmap b

match' :: PrismP s t a b -> s -> Either a t
match' pr = runUpStar (pr (UpStar Left))

build' :: PrismP s t a b -> b -> t
build' pr = unTagged . pr . Tagged

the' :: PrismP (Maybe a) (Maybe b) a b
the' = dimap (maybe (Right Nothing) Left) (either Just id) . left

-- Profunctor Affine

type AffineP s t a b = forall p . (Cartesian p, Cocartesian p) => Optic p s t a b

affineC2P :: Affine s t a b -> AffineP s t a b
affineC2P (Affine p st) = dimap preview' merge . left . rmap st . first where
  preview' s = either (\a -> Left (a, s)) Right (p s)
  merge = either id id

preview' :: AffineP s t a b -> s -> Either a t
preview' af = runUpStar (af (UpStar Left))

set' :: AffineP s t a b -> (b, s) -> t
set' af (b, s) = af (const b) s

maybeFirst' :: AffineP (Maybe a, c) (Maybe b, c) a b
maybeFirst' = first . dimap (maybe (Right Nothing) Left) (either Just id) . left

maybeFirst'' :: AffineP (Maybe a, c) (Maybe b, c) a b
maybeFirst'' = pi1' . the'

-- Profunctor Traversal

type TraversalP s t a b = forall p . (Cartesian p, Cocartesian p, Monoidal p) => Optic p s t a b

traversalC2P :: Traversal s t a b -> TraversalP s t a b
traversalC2P (Traversal c f) = dimap dup f . first . lmap c . ylw where
  ylw h = dimap (maybe (Right []) Left . uncons) merge $ left $ rmap cons $ par h (ylw h)
  cons = uncurry (:)
  dup a = (a, a)
  merge = either id id

contents' :: TraversalP s t a b -> s -> [a]
contents' tr = getConstant . runUpStar (tr (UpStar (\a -> Constant [a])))

firstNSecond' :: TraversalP (a, a, c) (b, b, c) a b
firstNSecond' pab = dimap group group' (first (pab `par` pab)) where
  group  (x, y, z) = ((x, y), z)
  group' ((x, y), z) = (x, y, z)
