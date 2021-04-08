module Category.Premonoidal.Free where

open import Data.List
open import Data.List.Properties using (++-monoid)
open import Relation.Binary.PropositionalEquality

open import Tactic.MonoidSolver using (solve)


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

  id : ∀ {xs}
     → Free xs xs
  id = zero

  _⟫_ : ∀ {xs ys zs}
      → Free xs ys
      → Free ys zs
      → Free xs zs
  zero ⟫ rs
    = rs
  suc pre q post qs ⟫ rs
    = suc pre q post (qs ⟫ rs)

  widen : ∀ {xs ys}
        → (pre : List X)
        → Free xs ys
        → (post : List X)
        → Free (pre ++ xs ++ post)
               (pre ++ ys ++ post)
  widen _ zero _
    = zero
  widen .{pre ++ input ++ post} .{ys}
        pre-pre
        (suc {input} {output} {ys} pre q post qs)
        post-post
    = subst (λ – → Free – _) (prf input)
        (suc {input} {output}
             {pre-pre ++ ys ++ post-post}
             (pre-pre ++ pre) q (post ++ post-post)
             (subst (λ – → Free – _) (sym (prf output))
               (widen pre-pre qs post-post)))
      where
        prf : ∀ xs
            → (pre-pre ++ pre) ++ xs ++ (post ++ post-post)
            ≡ pre-pre ++ (pre ++ xs ++ post) ++ post-post
        prf _ = solve (++-monoid X)

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
