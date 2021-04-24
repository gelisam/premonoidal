module Category.Premonoidal.Free where

import Category.SepBy
open import Data.List
open import Data.List.Properties using (++-monoid)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tactic.MonoidSolver using (solve)


module _ (X : Set)
         (Q : List X → List X → Set)
         where
  data Apply : List X → List X → Set where
    apply
      : ∀ {a b}
      → (pre : List X)
      → Q a b
      → (post : List X)
      → Apply (pre ++ a ++ post)
              (pre ++ b ++ post)

  widen-Apply
    : ∀ {pre-a-post pre-b-post}
    → (pre-pre : List X)
    → Apply pre-a-post pre-b-post
    → (post-post : List X)
    → Apply (pre-pre ++ pre-a-post ++ post-post)
            (pre-pre ++ pre-b-post ++ post-post)
  widen-Apply pre-pre (apply pre q post) post-post
    = subst (λ – → Apply – _) prf
    ( subst (λ – → Apply _ –) prf
    ( apply (pre-pre ++ pre) q (post ++ post-post)))
    where
      prf
        : {a : List X}
        → (pre-pre ++ pre) ++ a ++ (post ++ post-post)
        ≡ pre-pre ++ (pre ++ a ++ post) ++ post-post
      prf = solve (++-monoid X)

  open Category.SepBy _≡_ Apply _≡_
    renaming (SepBy to Free)

  propagate : ∀ {a b c z}
            → a ≡ b
            → b ≡ c
            → Apply c z
            → ∃ λ b′
            → ∃ λ c′
            → a ≡ b′
            × Apply b′ c′
            × c′ ≡ z
  propagate refl refl a-az
    = _ , _ , refl , a-az , refl

  open SepBy-Properties refl trans propagate
    renaming ( id-SepBy to id-Free
             ; compose-SepBy to compose-Free
             )

  widen-Free : ∀ {a b}
             → (pre : List X)
             → Free a b
             → (post : List X)
             → Free (pre ++ a ++ post)
                    (pre ++ b ++ post)
  widen-Free _ (zero refl) _
    = zero refl
  widen-Free pre (suc refl a-ab f-bz) post
    = suc refl
          (widen-Apply pre a-ab post)
          (widen-Free pre f-bz post)

  module _
         {R : List X → List X → Set}
         (id-R : ∀ {a}
               → R a a)
         (compose-R : ∀ {a b c}
                    → R a b
                    → R b c
                    → R a c)
         (let infixr 5 _⟫_; _⟫_ = compose-R)
         (runQ : ∀ {a b}
               → Q a b
               → R a b)
         (widen-R : ∀ {a b}
                  → (pre : List X)
                  → R a b
                  → (post : List X)
                  → R (pre ++ a ++ post)
                      (pre ++ b ++ post))
         (runQ : ∀ {a b}
               → Q a b
               → R a b)
         where
    runEq
      : ∀ {a b}
      → a ≡ b
      → R a b
    runEq refl
      = id-R

    runApply
      : ∀ {a b}
      → Apply a b
      → R a b
    runApply (apply pre q post)
      = widen-R pre (runQ q) post

    runFree
      : ∀ {a b}
      → Free a b
      → R a b
    runFree
      = runSepBy
          compose-R
          runEq
          runApply
          runEq
