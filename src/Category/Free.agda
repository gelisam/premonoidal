module Category.Free where

open import Category


postulate K : Object → Object → Set

data Free : Object → Object → Set where
  []  : ∀ {a}
      → Free a a
  _∷_ : ∀ {a b c}
      → K a b
      → Free b c
      → Free a c
