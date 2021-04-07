module Category.Premonoidal.Free where

open import Data.Nat
open import Data.List


module _ (K : Set)
         (Q : List K → List K → Set)
         where
  data Free : List K → List K → Set where
    zero
      : ∀ {i}
      → Free i i
    suc
      : ∀ {pre input output post j}
      → Q input output
      → Free (pre ++ output ++ post) j
      → Free (pre ++ input ++ post) j
