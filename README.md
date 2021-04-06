# Premonoidal

I want to constructively define a canonical representative for each equivalence class in a {,symmetric,semicartesian,cartesian} premonoidal category.

In Agda (this project), this makes it possible to define solvers which automatically prove that equivalent expressions (expressions in the same equivalence class) are equal.

In Haskell (my [category-syntax](https://github.com/gelisam/category-syntax#readme) project), this makes it easier to generate code which requires the minimal number of typeclasses.

Tested with Agda-2.6.1.1 and agda-stdlib-1.4.

* [Canonical Representatives and Solvers](#canonical-representatives-and-solvers)
* [Canonical Representative vs Free Category](#canonical-representative-vs-free-category)
* [Monoidal Categories vs Premonoidal Categories](#monoidal-categories-vs-premonoidal-categories)
* [Premonoidal Hierarchy](#premonoidal-hierarchy)

## Canonical Representatives and Solvers

The following equation holds in any category:

    (id >>> f) >>> (g >>> id)   ≡   f >>> id >>> g

My [category solver](src/Category/Solver.agda) can automatically prove that equation. That page explains the technique in details, but one key step is to transform both of those sides into a canonical representation, `f >>> (g >>> id)`.

Similarly, there are some equations which hold in any [symmetric premonoidal category](#symmetric-premonoidal-categories):

         a  (b  (c   d))                    a  (b  (c  d))
         |   |   |   |                      |   |   |  |
         |   |    \ /                       | ( |  (|  |))
         |   |     X                        | ((|   |) | )
         |   |    / \                       |    \ /   |
         |  (|  (|   |))                    |     X    |
        (|   |) (|   |)                     |    / \   |
          \ /    |   |                      | ((|   |) | )
          +-+    |   |                      | ( |  (|  |))
          |f|    |   |                     (|   |) (|  |)
          +-+    |   |                       \ /    |  |
           |      \ /           ≡             x     |  |
           |       X                         / \    |  |
           |      / \                      (|   |) (|  |)
           |    (|   |)                     | ( |  (|  |))
          (|     |)  |                      | ((|   |) | )
            \   /    |                      |    \ /   |
             \ /     |                      |    +-+   |
              X      |                      |    |f|   |
             / \    |                       |    +-+   |
           (|   |) |                        |     |    |
            |  (|  |)                       |     |    |
            |   |  |                        |     |    |
            c  (e  d)                       c    (e    d)

        second (second swap)               second (sym reassoc)
    >>> sym reassoc                    >>> second (first swap)
    >>> first f                        >>> second reassoc
    >>> second swap             ≡      >>> sym reassoc
    >>> sym reassoc                    >>> first swap
    >>> first swap                     >>> reassoc
    >>> reassoc                        >>> second (sym reassoc)
                                       >>> second (first f)

The same technique should work there too, but it's a lot less obvious which canonical representation we should pick. The goal of this repo is to figure out how to define such a canonical representation for the following classes of categories:

1. Premonoidal category
1. Symmetric premonoidal category
1. Semicartesian premonoidal category
1. Cartesian premonoidal category

## Canonical Representative vs Free Category

I used to frame the problem as "define a free premonoidal category", but the problem with that statement is that it has an easy solution which works with any typeclass:

    data EasyFreeCategory k a b where
      EasyFreeCategory
        :: ( forall c. Category c
          => (forall x y. k x y -> c x y)
          -> c a b
           )
        -> EasyFreeCategory k a b

This is technically a free `Category`: for example, `EasyFreeCategory (\_ -> id >>> id)` is equivalent to `EasyFreeCategory (\_ -> id)` because I'm only allowed to observe any differences by instantiating `c` to a type which has a valid `Category` instance, and thus for which `id >>> id = id`. But we learn nothing about free categories by looking at this definition. By contrast, consider the following definition:

    data FreeCategory k a b where
      Nil  :: FreeCategory k a a
      Cons :: k a b
           -> FreeCategory k b c
           -> FreeCategory k a c

This definition gives a lot more insight into the structure of the free category: clearly, it has the same structure as a list, and so we can probably apply similar kinds of transformations to it. Each value of type `FreeCategory`, e.g. `Cons f (Cons g Nil)`, also corresponds to an obvious canonical element in the equivalence class it represents, in this case `f >>> (g >>> id)`. Thus, the new way in which I am phrasing the problem is: "find a canonical representative for each equivalence class in a premonoidal category".

## Monoidal Categories vs Premonoidal Categories

Solvers are pretty cool, but why am I interested in writing a solver for _premonoidal_ categories? Wouldn't it make more sense to write a solver for _monoidal_ categories, which are a lot more commonly-discussed?

Well, my primary motivation isn't solvers, but my Haskell project [category-syntax](https://github.com/gelisam/category-syntax#readme). That project takes a pointful computation expressed using a variant of the Arrow notation, e.g.

    expr = proc (a, (b, (c, d))) -> do
      e <- f -< (a, b)
      returnC (c, (e, d))

and converts it into a pointfree expression which rearranges its variables using a number of methods like `swap` and `reassoc`:

    expr :: forall k. Symmetric k
         => k (a, b) e
         -> k (a, (b, (c, d))) (c, e, d)
    expr f
       -- (a, (b, (c, d)))
        = reassocL
       -- ((a, b), (c, d))
      >>> first f
       -- (e, (c, d))
      >>> reassocL
       -- ((e, c), d)
      >>> first swap
       -- ((c, e), d)
      >>> reassocR
       -- (c, (e, d))

The difference between monoidal and premonoidal categories is that in a monoidal category, the following law must hold.

            |   |             |   |             |   |
           +-+  |             |   |             |  +-+
           |f|  |            +-+ +-+            |  |g|
           +-+ +-+        =  |f| |g|  =        +-+ +-+
            |  |g|           +-+ +-+           |f|  |
            |  +-+            |   |            +-+  |
            |   |             |   |             |   |

    first f >>> second g  =  f *** g  =  second g >>> first f

That is, if two operations apply to different portions of the input, then in a monoidal category, it doesn't matter in which order the operations are applied, whereas in a premonoidal category, the order can be important.

Since the Arrow notation requires users to specify their operations one at a time, in order, I would like to allow my users to instantiate `k` to a type like `Kleisli IO`, in which that order is important because it specifies the order in which the side-effects occur. One alternative to that is Conal Elliott's [Compiling to Categories](http://conal.net/papers/compiling-to-categories/) approach, in which the input syntax is a lambda expression, which doesn't specify an order. With that syntax, monoidal categories would make more sense, but there are fewer types at which `k` could be instantiated.

## Premonoidal Hierarchy

Here's another string diagram.

    a   b    c
    |   |    |
     \ /     | 
     +-+     |
     |f|     |
     +-+     |
      |      |
      e      |
      |     / \
       \   /   |
        \ /    |
         X     c
        / \    |
       |   |  +-+
       |   |  |g|
       |   |  +-+
       |   |   |
       |   |   d
       |   |   |
       |   |   .
       |   |
       c   e


Note how the `c` and `e` wires cross, how the `c` wire splits into two `c` wires, and how the `d` wire ends before reaching the output.

In a free premonoidal category, the wires are not allowed to do any of that.

In a free symmetric premonoidal category, they are allowed to cross.

In a free semicartesian premonoidal category, they are also allowed to end before reaching the output.

In a free cartesian premonoidal category, they are also allowed to split in two.

That is, each of the classes of premonoidal categories I am interested in is strictly more expressive than the previous one. In category-syntax, I model this as a tower of typeclasses, each of which adds a new method, e.g. `Cartesian` adds `dup :: k a (a, a)` for splitting wires, which corresponds to using a variable more than once. I want to generate pointfree code which uses the least-expressive typeclass possible, so that the `k` can be instantiated to as many types as possible. That is, I prefer to output this:

    expr :: forall k. Symmetric k
         => k (a, b) e
         -> k (a, (b, (c, d))) (c, e, d)
    expr f
       -- (a, (b, (c, d)))
        = reassocL
       -- ((a, b), (c, d))
      >>> first f
       -- (e, (c, d))
      >>> reassocL
       -- ((e, c), d)
      >>> first swap
       -- ((c, e), d)
      >>> reassocR
       -- (c, (e, d))

than to output that:

    expr :: forall k. Cartesian k
         => k (a, b) e
         -> k (a, (b, (c, d))) (c, e, d)
    expr f
       -- (a, (b, (c, d)))
        = first dup
      >>> ((a, a), (b, (c, d)))
        = reassocR
       -- (a,  (a, (b, (c, d))))
      >>> second (second (first dup))
       -- (a,  (a, (b, ((c, c), d))))
      >>> ...
       -- ((a, c),  (a, (b, (c, d))))
      >>> first f
       -- (e, (a, (b, (c, d))))
      >>> ...
       -- ((c, (e, d)),  (e, (a, (b, (c, d)))))
      >>> fst
       -- (c, (e, d))

However, I don't want to write four different code-generation algorithms! I would prefer to output the `Cartesian` version, and then attempt to simplify it to a version which only requires the Semicartesian typeclass, then only Symmetric, then only Premonoidal, then only Category; stopping at some point along the way, when further simplification is not possible.

That's why I am looking for canonical representatives. First, find the representatives. Then, use them to define types like `FreeSymmetric`, `FreeSemicartesian` etc. in the style of `FreeCategory`, not `EasyFreeCategory`. With that style, I can pattern-match on the construction in order to attempt to simplify it to the next free construction, and then the next, etc. Then generate the code.

That being said, I've been working on this for years, so maybe I should just give up and write four code-generation algorithms? Probably, but it's not the destination which counts, it's the lemmas you prove along the way ;)
