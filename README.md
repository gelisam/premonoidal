# Premonoidal

A repository of Agda proofs which will help me to finish one of my Haskell libraries, [category-syntax](https://github.com/gelisam/category-syntax#readme).

*   [What?](#what)
    *   [Progress](#progress)
    *   ["Suitable representation"](#suitable-representation)
    *   ["Free enough"](#free-enough)
*   [Why?](#why)
    *   [Monoidal hierarchy](#monoidal-hierarchy)
    *   [Premonoidal hierarchy](#premonoidal-hierarchy)
    *   [Binoidal categories](#binoidal-categories)

## What?

The goal of this repo is to model the following classes of categories, and for each category class `C`, to find a suitable representation for a free `C`. Finally, I also want to prove that this representation is free enough.

1. Plain category
1. Binoidal category
1. Premonoidal category
1. Symmetric premonoidal category
1. Semicartesian premonoidal category
1. Cartesian premonoidal category

### Progress
  
1.  Plain category
    1. [x] model
    1. [x] suitable representation
    1. [ ] free enough
1.  Binoidal category
    1. [x] model
    1. [ ] suitable representation
    1. [ ] free enough
1.  Premonoidal category
    1. [ ] model
    1. [ ] suitable representation
    1. [ ] free enough
1.  Symmetric premonoidal category
    1. [ ] model
    1. [ ] suitable representation
    1. [ ] free enough
1.  Semicartesian premonoidal category
    1. [ ] model
    1. [ ] suitable representation
    1. [ ] free enough
1.  Cartesian premonoidal category
    1. [ ] model
    1. [ ] suitable representation
    1. [ ] free enough

### "Suitable representation"

By "suitable representation", I mean one which can be implemented in Haskell and which uses constructors and type parameter constraints in order to make sure that there is only one value for each equivalence class of morphisms. I mention this because there is an easy way to define a free `C` using functions constrained by a `C` typeclass, but this easy definition does not suit my purpose. Here is that easy definition for a free `Category`:

    data EasyFreeCategory k a b where
      EasyFreeCategory
        :: forall k. Category c
        => (forall x y. k x y -> c x y)
        -> c a b
        -> EasyFreeCategory k a b

This is technically a free `Category`: for example, `EasyFreeCategory (\_ -> id >>> id)` is equivalent to `EasyFreeCategory (\_ -> id)` because I'm only allowed to observe any differences by instantiating `c` to a type which has a valid `Category` instance, and thus for which `id >>> id = id`. But we learn nothing about free categories by looking at this definition. By contrast, consider the following definition:

    data FreeCategory k a b where
      Nil  :: FreeCategory k a a
      Cons :: k a b
           -> FreeCategory k b c
           -> FreeCategory k a c

It is less obvious that this definition is indeed a free `Category`, which is why I want to write a proof in order to make sure. But assuming that this definition is correct, this time we learn a lot more: we learn that the free `Category` is very similar to a list, the free `Monoid`. Knowing this is very helpful, e.g. given an equality decider for `k`, we can now write an equality decider for `FreeCategory k`.

For two category classes `C1` and `C2` which are consecutive in the above list, I want to write an algorithm determining whether a given morphism in `FreeC2` can be encoded in `FreeC1` as well. This will allow category-syntax to generate code in the least powerful category in which the input program can be expressed.

### "Free enough"

If `C` demands that two expressions e.g. `(f >>> g) >>> h` and `f >>> (g >>> h)` must be equal, then if `f`, `g` and `h` are all `FreeC k` values, I would like `(f >>> g) >>> h` and `f >>> (g >>> h)` to normalize to the same `FreeC k` value. Sounds straightforward, but consider the following attempt:

    data Tree a xs where
      Leaf   :: Tree a [a]
      Branch :: Tree a as
             -> Tree b bs
             -> Tree (a, b) (as ++ bs)

    data Step k a b where
      Step :: Tree xay (xs ++ as ++ ys)
           -> Tree a as
           -> k a b
           -> Tree b bs
           -> Tree xby (xs ++ bs ++ ys)
           -> Step k xay xby

    data FreePremonoidalCategory k a b where
      Nil  :: Tree a xs
           -> Tree b xs
           -> FreePremonoidalCategory k a b
      Cons :: Step k a b
           -> FreePremonoidalCategory k b c
           -> FreePremonoidalCategory k a c

The idea behind `Tree a xs` is to capture the idea that the parentheses don't matter. For example, the types `((a, b), c)` and `(a, (b, c))` only differ in the placement of the parentheses, and so there are two `Tree`s

    Branch (Branch Leaf Leaf) Leaf :: Tree ((a, b), c) [a,b,c]
    Branch Leaf (Branch Leaf Leaf) :: Tree (a, (b, c)) [a,b,c]

relating them by showing that they both contain the list of types `[a,b,c]`. I can then use those `Tree`s as arguments to `Nil` to construct a morphism which goes from one type to the other without applying any `k`-morphism.

There are two problems with the above attempt. The first is that there are multiple ways to represent the identity morphism over the type `(a, b)`: we could use `Nil Leaf Leaf`, or we could use `Nil (Branch Leaf Leaf) (Branch Leaf Leaf)`. It might be possible to forbid the first one by insisting that `Nil` may only be used on non-product types, but that would make it tricky to write polymorphic code, and so I prefer to allow this ambiguity. This is why I only want to prove that my representation is free "enough".

The other issue is more problematic. Every step may arbitrarily rearrange its parentheses in order to get the inputs of `k a b` in the right format, which is good, but the parts of `xay` which aren't fed to `k a b` may also be unnecessarily arranged, which means that there is more than one way to represent a given composition of `k`-morphisms.

Since I want to allow more than one representation in one case but not in the other, I will have to find a way to define the difference more formally in order to prove that my data type definitions are free enough.

## Why?

In category-syntax, I want to interpret a do-notation block into an arbitrary category. The Category typeclass is only expressive enough to encode composition, so depending on what happens within that do-notation block, some extra typeclasses will be required.

### Monoidal hierarchy

Originally, I was planning to model those extra typeclasses on well-known classes of categories:

1.  A plain category if the output of each step in the do-notation block is directly given to the next step, and then never used again. This leads to a string diagram consisting of a straight line. For example:

                              A
                              |
        do a <- getInput      f
           b <- f a           |
           c <- g b           g
           d <- h c           |
           returnC d          h
                              |
                              D

1.  A monoidal category if some steps produce a tuple of values, each of which is used exactly once, which can be used to draw a string diagram in which the strings never cross. For example:

                                          A    BC  Z  D
                                          |    |   |  |
        do (a, bc, z, d) <- getInput      |    f   |  |
           (b, c) <- f bc                 |   / \  g  |
           () <- g z                      |  |   \   /
           cd <- h (c, d)                 |  |    \ /
           returnC (a, b, cd)             |  |     h
                                          |  |     |
                                          A  B     CD

1.  A symmetric monoidal category if the strings do cross. In this model, every variable is a linear resource, which must be used exactly once. For example:

                                            CB  Z  D  A
                                            |   |  |  |
                                            f   |  |  |
                                           / \  |  |  |
                                           \  | |  |  |
        do (cb, z, d, a) <- getInput        \ | g  | /
           (c, b) <- f cb                    \|    |/
           () <- g z                          |\  /|
           cd <- h (c, d)                     | \/ |
           returnC (a, b, cd)                 | /\ |
                                              |/  \|
                                             /|    h
                                            | |    |
                                            A B    CD

1.  A semicartesian monoidal category if some of the variables are unused, leading to a string diagram in which some of the lines stop before reaching the output. In this model, every variable is an affine resource, which can be used at most once. For example:

                                           CB  Z  D  A
                                           |   |  |  |
                                           f   |  |  |
                                          / \  |  |  |
                                          \  | |  |  |
        do (cb, z, d, a) <- getInput       \ | .  | /
           (c, b) <- f cb                   \|    |/
           cd <- h (c, d)                    |\  /|
           returnC (a, b, cd)                | \/ |
                                             | /\ |
                                             |/  \|
                                            /|    h
                                           | |    |
                                           A B    CD

1.  A cartesian category if some of the variables are used more than once, leading to a string diagram in which some of the lines fork. In this model, variables can be used as many times as needed, including zero times. For example:

                                            CB  Z  D  A
                                            |   |  |  |
                                            |   |  |  *
                                            |   |  | /|
                                            |   .  |/ |
                                            |     /|  |
                                            |    / |  |
                                            |   /  |  |
                                            |  /   |  |
                                            | /    |  |
        do (cb, z, d, a) <- getInput        |/     |  |
           (c, b) <- f (cb, a)              f      |  |
           cd <- h (c, d)                  / \     |  |
           returnC (a, b, cd)              \  |    |  |
                                            \ |    | /
                                             \|    |/
                                              |\  /|
                                              | \/ |
                                              | /\ |
                                              |/  \|
                                             /|    h
                                            | |    |
                                            A B    CD

### Premonoidal hierarchy

In a monoidal category, one of the laws which hold is that `first f >>> second g` = `f *** g` = `second g >>> first f`. This law does not hold for `Kleisli IO`, because in `first f >>> second g`, the side-effects of `f` occur first, whereas in `second g >>> first f`, they occur last. This means that `Kleisli IO` is not a monoidal category. So if I want to be able to use category-syntax's linear resource semantics to e.g. guarantee that we don't write to a linear file handle after we've closed it, I won't be able to instantiate such a guaranteed-correct block to IO in order to run it on an actual file. This does not work at all.

So instead of the above hierarchy of well-known category classes, I must instead use the much less well-known hierarchy I gave in the "What" section:

1. Plain category
1. Binoidal category
1. Premonoidal category
1. Symmetric premonoidal category
1. Semicartesian premonoidal category
1. Cartesian premonoidal category

The restrictions and the example diagrams are the same as for their monoidal counterparts. The interpretation of those diagrams is the same, too. The only difference is that fewer laws apply in premonoidal categories than in monoidal categories, and so this affects which pairs of diagrams are considered equivalent. In a monoidal monoidal category, we can freely slide morphisms along their edges, so those three diagrams are equivalent:

    A  B        A  B        A  B
    |  |        |  |        |  |
    f  |        |  |        |  g
    |  |        f  g        |  |
    |  g        |  |        f  |
    |  |        |  |        |  |
    A  B        A  B        A  B

Whereas in a premonoidal category, the middle diagram is disallowed, and the remaining diagrams are not considered equivalent.

Since the premonoidal hierarchy is less well-known than the monoidal hierarchy, I am not sure if I'll find reference material defining all the laws which must hold in each class of categories. So the first step is to carefully model those category classes, by adapting the definitions from their more well-known monoidal counterparts, making sure to only encode the laws which are still valid in the premonoidal setting. Then, I will come up with data type definitions in the style of `FreePremonoidalCategory` above, and then prove that these definitions are free enough. If so, I will then use those data type definitions in category-syntax.

### Binoidal categories

The premonoidal hierarchy has one more level than the monoidal hierarchy: binoidal categories. There is no theoretical reason for that inconsistency, it just happens that the monoidal equivalent to a binoidal category, which I would call a "bifunctorial category", is pretty much never used and so I could not find an existing name for it. It is, however, easy to define: just like a monoidal category, a bifunctorial category is a category equipped with a bifunctor named "tensor". Unlike a monoidal category, however, the definition stops there, we do not also postulate the existence of morphisms witnessing the associativity of the tensor, nor the existence of an identity object.

In terms of string diagrams, this restricts which strings we are allowed to attach to one another. I like to imagine strings being surrounded by tubes, and so if new strings are created inside a tube, they can interact with each other, but they cannot interact with anything outside of their tube.

                                             A                 BCD
                                            (|)                (|)
                                           ( | )               (f)
                                          (  |  )             (/ \)
                                          (  |  )            (/) (\)
                                          (  |  )           (/)   (\)
                                          (  |  )          (/)     (\)
                                          (  |  )         (/)       (\)
                                          (  |  )        (/)         (\)
                                          (  |  )       (|)           (|)
                                          (  |  )      ( | )         ( | )
                                          (  |  )     (  |  )       (  |  )
                                          (  |  )     (  |  )      (   |   )
                                          (  |  )     (  |  )     (    |    )
        do (a, bcd) <- getInput           (  |  )     (  |  )    (     g     )
           (b, cd) <- f bcd               (  |  )     (  |  )    (   (/ \)   )
           (c, d) <- g cd                 (  |  )     (  |  )    (  (|) (|)  )
           cd' <- h (c, d)                (  |  )     (  |  )    (   (\ /)   )
           bcd' <- i (b, cd')             (  |  )     (  |  )    (     h     )
           returnC (a, bcd')              (  |  )     (  |  )     (    |    )
                                          (  |  )     (  |  )      (   |   )
                                          (  |  )     (  |  )       (  |  )
                                          (  |  )      ( | )         ( | )
                                          (  |  )       (|)           (|)
                                          (  |  )        (\)         (/)
                                          (  |  )         (\)       (/)
                                          (  |  )          (\)     (/)
                                          (  |  )           (\)   (/)
                                          (  |  )            (\) (/)
                                          (  |  )             (\ /)
                                           ( | )               (i)
                                            (|)                (|)
                                             A                 BCD'

I don't expect binoidal categories to be much more useful than bifunctorial categories, but they are certainly simpler to model than premonoidal categories. This is why I include them in my plan: I want to proceed in small increments. I have not yet decided whether I want to include them in category-syntax.
