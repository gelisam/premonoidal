module Category.Premonoidal.Free where

open import Data.Nat
open import Data.List


module _ (X : Set)
         (Q : List X → List X → Set)
         where
  data Free : List X → List X → Set where
    zero
      : ∀ {xs}
      → Free xs xs
    suc
      : ∀ {input output ys}
      → (pre : List X)
      → Q input output
      → (post : List X)
      → Free (pre ++ output ++ post) ys
      → Free (pre ++ input ++ post) ys

  module _
         (R : List X → List X → Set)
         (id : ∀ {xs}
             → R xs xs)
         (_⟫_ : ∀ {xs ys zs}
              → R xs ys
              → R ys zs
              → R xs zs)
         (widen : ∀ {xs ys}
                → (pre : List X)
                → R xs ys
                → (post : List X)
                → R (pre ++ xs ++ post)
                    (pre ++ ys ++ post))
         (runQ : ∀ {xs ys}
               → Q xs ys
               → R xs ys)
         where
    runFree
      : ∀ {xs ys}
      → Free xs ys
      → R xs ys
    runFree zero
      = id
    runFree (suc pre q post qs)
      = widen pre (runQ q) post
      ⟫ runFree qs
