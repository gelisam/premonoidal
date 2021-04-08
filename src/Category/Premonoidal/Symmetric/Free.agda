module Category.Premonoidal.Symmetric.Free where

open import Data.Nat
open import Data.List
open import Data.List.Properties using (++-monoid)
open import Relation.Binary.PropositionalEquality

open import Tactic.MonoidSolver using (solve)


module _ (X : Set)
         (Q : List X → List X → Set)
         where
  data PickOne : List X → X → List X → Set where
    here
      : ∀ {r xs}
      → PickOne (r ∷ xs) r xs
    there
      : ∀ {r x xs ys}
      → PickOne xs r ys
      → PickOne (x ∷ xs) r (x ∷ ys)

  data PickMany : List X → List X → List X → Set where
    []
      : ∀ {xs}
      → PickMany xs [] xs
    _∷_
      : ∀ {r rs xs ys zs}
      → PickOne xs r ys
      → PickMany ys rs zs
      → PickMany xs (r ∷ rs) zs

  Rearrange : List X → List X → Set
  Rearrange xs ys = PickMany xs ys []

  data Free : List X → List X → Set where
    zero
      : ∀ {xs ys}
      → Rearrange xs ys
      → Free xs ys
    suc
      : ∀ {xs input output suffix ys}
      → PickMany xs input suffix
      → Q input output
      → Free (output ++ suffix) ys
      → Free xs ys
