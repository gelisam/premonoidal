-- | A free monoidal category over a monoidal signature Q.
--
-- The main difference between a premonoidal category and a monoidal category is
-- that the latter obeys this equation:
--
-- > ((f ⊗ id) >>> (id ⊗ g)) = (f ⊗ g) = ((id ⊗ g) >>> (f ⊗ id))
--
-- >   |     |         |     |         |     |
-- > +---+   |         |     |         |   +---+
-- > | f |   |         |     |         |   | g |
-- > +---+   |       +---+ +---+       |   +---+
-- >   |     |    =  | f | | g |  =    |     |
-- >   |   +---+     +---+ +---+     +---+   |
-- >   |   | g |       |     |       | f |   |
-- >   |   +---+       |     |       +---+   |
-- >   |     |         |     |         |     |
--
-- That is, generators can slide up and down their wire of identity morphisms.
--
-- In a free monoidal category over a _quiver_, generators always take a single
-- input and produce a single output. Thus, generators on different wires don't
-- interact with each other, so a simple normal form is simply to stack the
-- generators into one pile per wire:
--
-- >   |     |     |     |     |
-- > +---+   |   +---+   |   +---+
-- > | f |   |   | g |   |   | h |
-- > +---+   |   +---+   |   +---+
-- >   |     |     |     |     |
-- >   |   +---+ +---+ +---+   |
-- >   |   | i | | j | | k |   |
-- >   |   +---+ +---+ +---+   |
-- >   |     |     |     |     |
-- > +---+ +---+ +---+   |     |
-- > | l | | m | | n |   |     |
-- > +---+ +---+ +---+   |     |
-- >   |     |     |     |     |
--
-- Normalizes to:
--
-- >   |     |     |     |     |
-- >   |     |   +---+   |     |
-- >   |     |   | g |   |     |
-- >   |     |   +---+   |     |
-- > +---+ +---+ +---+   |     |
-- > | f | | i | | j |   |     |
-- > +---+ +---+ +---+   |     |
-- > +---+ +---+ +---+ +---+ +---+
-- > | l | | m | | n | | k | | h |
-- > +---+ +---+ +---+ +---+ +---+
--
-- We can think of the normalization process as letting gravity pull the
-- generators down to the lowest possible position, either the floor or another
-- generator, thus eliminating their degree of freedom to slide up and down.
--
-- For a free monoidal category over a _monoidal signature_, generators can have
-- multiple inputs and multiple outputs, and thus slide up and down multiple
-- wires. This causes the generators to interact in a more complicated way, but
-- the basic idea is the same: the normal form is obtained by letting gravity
-- pull the generators down to the lowest possible position, either the floor or
-- another generator. The result looks like a tetris game:
--
-- >      |              |     |
-- > +---------+ +---+   |   +---+
-- > |    f    | | g |   |   | h |
-- > +---------+ +---+   |   +---+
-- >   |     |     |     |     |
-- > +---+ +---+   |   +---------+
-- > | i | | j |   |   |    k    |
-- > +---+ +---+   |   +---------+
-- >   |     |     |     |     |
-- >   |   +---------------+   |
-- >   |   |       l       |   |
-- >   |   +---------------+   |
-- >   |        |     |        |
-- > +---+    +---+ +---+      |
-- > | m |    | n | | o |      |
-- > +---+    +---+ +---+      |
-- >   |        |     |        |
--
-- Normalizes to:
--
-- >      |              |     |
-- > +---------+         |   +---+
-- > |    f    |         |   | h |
-- > +---------+         |   +---+
-- >   |   +---+ +---+ +---------+
-- >   |   | j | | g | |    k    |
-- >   |   +---+ +---+ +---------+
-- > +---+ +---------------+   |
-- > | i | |       l       |   |
-- > +---+ +---------------+   |
-- > +---+    +---+ +---+      |
-- > | m |    | n | | o |      |
-- > +---+    +---+ +---+      |
--
-- String diagrams are normally drawn with the data flowing from top to bottom;
-- the implementation below can either be interpreted as implementing the above
-- Tetris-normalization idea if the data instead flows from bottom to top, or as
-- implementing a variation of the above Tetris-normalization idea where gravity
-- pulls the generators up instead of down.
module Category.Monoidal.Free where

open import Data.Empty
open import Data.List
open import Data.Unit


module _ (X : Set)
         (Q : List X → List X → Set)
         where
  data Support : Set where
    Supported : X → Support
    Unsupported : X → Support

  fromSupport : Support → X
  fromSupport (Supported x)
    = x
  fromSupport (Unsupported x)
    = x

  setSupported : Support → Support
  setSupported (Supported x)
    = Supported x
  setSupported (Unsupported x)
    = Supported x

  setUnsupported : Support → Support
  setUnsupported (Supported x)
    = Unsupported x
  setUnsupported (Unsupported x)
    = Unsupported x

  SupportList : Set
  SupportList = List Support

  toSupportedList : List X → SupportList
  toSupportedList []
    = []
  toSupportedList (x ∷ xs)
    = Supported x
    ∷ toSupportedList xs

  fromSupportList : SupportList → List X
  fromSupportList []
    = []
  fromSupportList (sx ∷ xs)
    = fromSupport sx
    ∷ fromSupportList xs

  someSupport : SupportList → Set
  someSupport []
    = ⊥
  someSupport (Supported _ ∷ _)
    = ⊤
  someSupport (Unsupported _ ∷ xs)
    = someSupport xs

  data Layer : SupportList → SupportList → Set where
    Nil
      : Layer [] []
    Blank
      : ∀ {sx sxs sys}
      → Layer sxs sys
      → Layer (sx ∷ sxs) (setUnsupported sx ∷ sys)
    Block
      : ∀ {sinput output sxs sys}
      → Q (fromSupportList sinput) output
      → someSupport sinput  -- make sure the Q block is supported
      → Layer sxs sys
      → Layer (sinput ++ sxs) (toSupportedList output ++ sys)

  data Tetris : SupportList → SupportList → Set where
    Nil
      : ∀ {sxs}
      → Tetris sxs sxs
    Cons
      : ∀ {sxs sys szs}
      → (layer : Layer sxs sys)
      → someSupport sys  -- make sure the layer is not empty
      → Tetris sys szs
      → Tetris sxs szs

  data Free (xs : List X) : List X → Set where
    MkFree
      : ∀ {sys}
      → Tetris (toSupportedList xs) sys
      → Free xs (fromSupportList sys)