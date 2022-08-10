# Don't Fear the Profunctor Optics (Part 1/3)

It is said that [profunctors are so easy](https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/profunctors). What about [profunctor optics](http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf)? They should be easy too, right? However, it might be a little bit scary and confusing to face a definition such as

```haskell
type LensP s t a b = forall p . Cartesian p => p a b -> p s t
```

for the very first time. In this series, we'll try to introduce all the required concepts that you need to understand this alias (and other ones). To do so, we'll provide visual diagrams where profunctors are seen as boxes which take inputs and produce outputs and profunctor optics are just functions that transform those boxes into more complex ones. Prior to that, a brief introduction to optics will be supplied. We hope these resources help you to never ever fear the profunctor optics.

## Optics, Concretely

Optics are essentially abstractions to update immutable data structures in an elegant way. Besides profunctor, there are [many other optic representations](https://www.twanvl.nl/files/lenses-talk-2011-05-17.pdf). The original one, also known as *concrete*, is perhaps the most accessible for a newcomer. Thereby, we'll introduce optics using this representation and later, the same examples will be translated into profunctor optics. Although not the simplest one, *Lens* has become the most famous optic, so we'll start by describing it.

### Lens

Informally, lenses are useful to access a certain *focus* value which is contextualized in a bigger *whole* value. What do we mean by "access" here? At least, we'd like to be able to view and update the focus, given an original whole value. Translating this requirements into code, we get our initial lens definition where `s` is the whole and `a` is the focus:

```haskell
data Lens s a = Lens { view   :: s -> a
                     , update :: (a, s) -> s }
```

The typical lens example is `π1`, which access the first component (the focus) of a 2-tuple (the whole):

```haskell
π1 :: Lens (a, b) a
π1 = Lens v u where
  v = fst
  u (a', (_, b)) = (a', b)
```

We provide an usage example as well:

```haskell
λ> view π1 (1, 'a')
1
λ> update π1 (2, (1, 'a'))
(2,'a')
```

This is nice, but we could do better. What if we teach our lenses to morph the type of the focus (and consequently, the type of the whole)? I mean, what if we want to replace `1` with `"hi"` in the previous example? To do so, we need to slightly modify our former lens definition, in order to support [this kind of polymorphism](http://r6.ca/blog/20120623T104901Z.html):

```haskell
data Lens s t a b = Lens { view   :: s -> a
                         , update :: (b, s) -> t }
```

As a result, `π1` turns into:

```haskell
π1 :: Lens (a, c) (b, c) a b
π1 = Lens v u where
  v = fst
  u (b, (_, c)) = (b, c)
```

Surprisingly, both versions share the same implementation, but notice the change in the signature. Now, we can use our new lens in a polymorphic way:

```haskell
λ> update π1 ("hi", (1, 'a'))
("hi",'a')
```

It is worth mentioning that lenses should hold a few laws:

```haskell
viewUpdate :: Eq s => Lens s s a a -> s -> Bool
viewUpdate (Lens v u) s = u ((v s), s) == s

updateView :: Eq a => Lens s s a a -> a -> s -> Bool
updateView (Lens v u) a s = v (u (a, s)) == a

updateUpdate :: Eq s => Lens s s a a -> a -> a -> s -> Bool
updateUpdate (Lens v u) a1 a2 s = u (a2, (u (a1, s))) == u (a2, s)
```

Informally, these laws check that `update` is exclusively modifying the focus and that `view` extracts that focus value as is.

You might be thinking that lenses are not necessary to achieve such a simple task. Why should we care about them? The thing is that they have become very handy to deal with nested immutable data structures. In fact, this is a direct consequence of one of the major features of optics: they compose! As an example, we could compose lenses to update the first component of a 2-tuple which is surrounded by additional 2-tuple layers:

```haskell
λ> update (π1 |.| π1 |.| π1) ("hi", (((1, 'a'), 2.0), True))
((("hi",'a'),2.0),True)
```

The composition method is implemented as follows:

```haskell
(|.|) :: Lens s t a b -> Lens a b c d -> Lens s t c d
(Lens v1 u1) |.| (Lens v2 u2) = Lens v u where
  v = v2 . v1
  u (d, s) = u1 ((u2 (d, (v1 s))), s)
```

Nevertheless, this way of composing optics is clumsy. This is evidenced when we try to compose lenses with other kinds of optics, where we require a different method for each kind we want to compose with. Consequently, libraries that use concrete representation become more verbose, and programmers that use this libraries require a deep knowledge on the composition interface. As we'll see in further sections, profunctor optics make composition trivial. For now, let's forget about composition and focus on getting comfortable with concrete optic operations.

### Adapter

The next optic that will be covered is *Adapter*. As its name suggests, this optic is able to adapt values. Particularly, it adapts the whole value to the focus value, and viceversa. In fact, this optic manifests that both whole and focus values contain the same information. The polymorphic representation for adapters is implemented this way:

```haskell
data Adapter s t a b = Adapter { from :: s -> a
                               , to   :: b -> t }
```

Adapters should obey some rules as well:

```haskell
fromTo :: Eq s => Adapter s s a a -> s -> Bool
fromTo (Adapter f t) s = (t . f) s == s

toFrom :: Eq a => Adapter s s a a -> a -> Bool
toFrom (Adapter f t) a = (f . t) a == a
```

Basically, they're telling us that this optic should behave as an isomorphism.

As an adapter example, we supply `shift`, which evidences that associativity changes in tuples aren't lossy:

```haskell
shift :: Adapter ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
shift = Adapter f t where
  f ((a, b), c) = (a, (b, c))
  t (a', (b', c')) = ((a', b'), c')
```

We show a simple usage scenario for `shift` in the next gist:

```haskell
λ> from shift ((1, "hi"), True)
(1,("hi",True))
λ> to shift (True, ("hi", 1))
((True,"hi"),1)
```

### Prism

`Prism` emerges when there's the possibility that the focus value isn't available, though we can always reassemble the whole value when given the focus. If you're familiar with algebraic datatypes, lenses deal with product types while prisms deal with sum types. Prisms are represented as follows:

```haskell
data Prism s t a b = Prism { match :: s -> Either a t
                           , build :: b -> t }
```

They have two operations: `match` and `build`. The first one tries to extract the focus value from the whole one, but if it's not possible, it provides the final value for `t`. On the other hand, `build` is always able to construct the whole value, given the focus one. As expected, this optic should hold the following properties:

```haskell
matchBuild :: Eq s => Prism s s a a -> s -> Bool
matchBuild (Prism m b) s = either b id (m s) == s

buildMatch :: (Eq a, Eq s) => Prism s s a a -> a -> Bool
buildMatch (Prism m b) a = m (b a) == Left a
```

They manifest the consistency between `match` and `build`: if we are able to view an existing focus, building it will return the original structure; if we build a whole from any focus, that whole must contain a focus.

A common prism is `the` that focuses on the value which is hidden behind a `Maybe` type, if any:

```haskell
the :: Prism (Maybe a) (Maybe b) a b
the = Prism (maybe (Right Nothing) Left) Just
```

Now, we can appreciate that it's not always possible to get the focus from a `Maybe` value, though we can build a whole `Maybe` if we have the focus, simply using `Just`:

```haskell
λ> match the (Just 1)
Left 1
λ> match the Nothing
Right Nothing
λ> build the 1
Just 1
λ> build the "hi"
Just "hi"
```

### Affine

There's a little-known optic which is a hybrid between lenses and prisms. It's known as [*Affine*](http://oleg.fi/gists/posts/2017-03-20-affine-traversal.html) or [Optional](http://julien-truffaut.github.io/Monocle/optics/optional.html). Like prisms, this optic expresses that the focus value might not exist. Like lenses, this optic expresses that, given the focus value, we should be able to build the whole value, but unlike prisms, we'd need context information to do so. In Haskell, this optic is encoded as follows:

```haskell
data Affine s t a b = Affine { preview :: s -> Either a t
                             , set     :: (b, s) -> t }
```

We can see two methods here: `preview` and `set`. As you might have noticed, this optic has borrowed prism's `match` and lens' `update`. The intuition behind these methods is the same that the one behind their counterparts. These are affine's laws:

```haskell
previewSet :: Eq s => Affine s s a a -> s -> Bool
previewSet (Affine p st) s = either (\a -> st (a, s)) id (p s) == s

setPreview :: (Eq a, Eq s) => Affine s s a a -> a -> s -> Bool
setPreview (Affine p st) a s = p (st (a, s)) == either (Left . const a) Right (p s)

setSet :: Eq s => Affine s s a a -> a -> a -> s -> Bool
setSet (Affine p st) a1 a2 s = st (a2, (st (a1, s))) == st (a2, s)
```

The intuition is pretty similar to the one behind prisms, but there's an important difference: when setting a value, it doesn't necessarily mean that `preview` will return it, but in case it does, the value will be exactly the one which was set. In fact, `set` only updates the whole structure if it does contain a focus value.

Here's an example of affine, which tries to access `a` in `(Maybe a, c)`:

```haskell
maybeFirst :: Affine (Maybe a, c) (Maybe b, c) a b
maybeFirst = Affine p st where
  p (ma, c) = maybe (Right (Nothing, c)) Left ma
  st (b, (ma, c)) = (ma $> b, c)
```

There's not always an `a` hidden behind this data structure. On the other hand, we can't build a whole `(Maybe b, c)` simply from a `b`. In fact, we need a `c` to do so. In addition, the affine laws make it impossible to update the focus if it didn't exist in the whole. Therefore, we need the complete `(Maybe a, c)` as contextual information. Next, we show a scenario where we run this optic:

```haskell
λ> preview maybeFirst (Just 1, "hi")
Left 1
λ> preview maybeFirst (Nothing, "hi")
Right (Nothing,"hi")
λ> set maybeFirst ('a', (Just 1, "hi"))
(Just 'a',"hi")
λ> set maybeFirst ('a', (Nothing, "hi"))
(Nothing,"hi")
```

Although we implemented `maybeFirst` in a monolithical way for pedagogical reasons, you have probably noticed that this example combines somehow `π1` with `the`. This intuition is nice and we'll come back to it in further parts, when we cover optic composition in detail.

### Traversal

Finally, *Traversal* will be introduced. This optic is very useful when the whole value contains a sequence of focus values of the same type. This includes the possibility of having zero, just one, or more than one focus values. Naively, we could try to represent a traversal as follows:

```haskell
data Traversal s t a b = Traversal { contents :: s -> [a]
                                   , fill     :: [b] -> s -> t }
```

Here, `contents` is responsible for getting all the focus values, while `fill` updates them. However, this way of representing traversals is wrong, since the number of focus values should be determined by `s` and must be consistent among `contents` and `fill`. For that reason, traversals are concretely represented with a [nested list](https://twanvl.nl/blog/haskell/non-regular1) coalgebra or a [store free applicative](https://bartoszmilewski.com/2015/07/13/from-lenses-to-yoneda-embedding/) coalgebra, where the aforementioned conditions are preserved. However, these definitions are beyond the scope of this post. From now on, we'll be using our fake traversal, since it provides a nice introductory intuition. Similarly, traversal laws won't be covered. As usual, we provide a traversal example:

```haskell
firstNSecond :: Traversal (a, a, c) (b, b, c) a b
firstNSecond = Traversal c f where
  c (a1, a2, _)  = [a1, a2]
  f (bs, (_, _, x)) = (head bs, (head . tail) bs, x)
```

This traversal includes the first and second components of a 3-tuple as focus values. Notice that the impure `fill` implementation is just a consequence of using our fake representation. Think of what would happen if we provided an empty list while filling. Anyway, here's how we use `firstNSecond`:

```haskell
λ> contents firstNSecond (1, 2, "hi")
[1,2]
λ> fill firstNSecond (['a', 'b'], (1, 2, "hi"))
('a','b',"hi")
```

### Conclusions

Today, we've introduced some of the most representative optics (along with their associated laws) in their concrete representation. They all hold the notion of focus and whole, which will be very useful when facing profunctor optics. On the other hand, we could appreciate that traversals are quite tricky. If you feel curious about the right way of representing them, you can read [this great article](https://arxiv.org/pdf/1103.2841.pdf) by Russell O'Connor, where they were firstly introduced. The next day, we'll cover profunctors, which suppose an intermediate step of preparation before dealing with profunctor optics.

NEXT: [Profunctors as Generalized Functions](Profunctors.md)
