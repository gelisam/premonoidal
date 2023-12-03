-- One approach to free symmetric premonoidal categories.
-- One downside of this approach is that 'Rearrange's change a lot when
-- composing two 'Free's.
module Category.Premonoidal.Symmetric.Free1 where

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

  rearrange-id
    : ∀ {xs}
    → Rearrange xs xs
  rearrange-id {[]}
    = []
  rearrange-id {_ ∷ _}
    = here ∷ rearrange-id

  id
    : ∀ {xs}
    → Free xs xs
  id
    = zero rearrange-id

  module _
         (R : List X → List X → Set)
         (id : ∀ {xs}
             → R xs xs)
         (_⟫_ : ∀ {xs ys zs}
              → R xs ys
              → R ys zs
              → R xs zs)
         (let infixr 5 _⟫_; _⟫_ = _⟫_)
         (widen : ∀ {xs ys}
                → (pre : List X)
                → R xs ys
                → (post : List X)
                → R (pre ++ xs ++ post)
                    (pre ++ ys ++ post))
         (swap : ∀ {x y}
               → R (x ∷ y ∷ [])
                   (y ∷ x ∷ []))
         (runQ : ∀ {xs ys}
               → Q xs ys
               → R xs ys)
         where
    first
      : ∀ {xs ys}
      → R xs ys
      → (suffix : List X)
      → R (xs ++ suffix)
          (ys ++ suffix)
    first r suffix
      = widen [] r suffix

    second
      : ∀ {xs ys}
      → (prefix : List X)
      → R xs ys
      → R (prefix ++ xs)
          (prefix ++ ys)
    second {xs} {ys} prefix r
      = subst (λ – → R – _) (prf xs)
          (subst (λ – → R _ –) (prf ys)
            (widen prefix r []))
      where
        prf : ∀ zs
            → prefix ++ zs ++ []
            ≡ prefix ++ zs
        prf _ = solve (++-monoid X)

    runPickOne
      : ∀ {xs r ys}
      → PickOne xs r ys
      → R xs (r ∷ ys)
    runPickOne here
      = id
    runPickOne .{x ∷ xs} .{r} .{x ∷ ys} (there {r} {x} {xs} {ys} pickOne)
        -- x ∷ xs
      = second (x ∷ []) (runPickOne pickOne)
        -- x ∷ r ∷ ys
      ⟫ first swap ys
        -- r ∷ x ∷ ys

    runPickMany
      : ∀ {xs rs ys}
      → PickMany xs rs ys
      → R xs (rs ++ ys)
    runPickMany []
      = id
    runPickMany (pickOne ∷ pickMany)
     -- xs
      = runPickOne pickOne
     -- r ∷ ys
      ⟫ second (_ ∷ [])
               (runPickMany pickMany)
     -- r ∷ rs ++ zs

    runFree
      : ∀ {xs ys}
      → Free xs ys
      → R xs ys
    runFree (zero rearrange)
      = subst (λ – → R _ –) prf
          (runPickMany rearrange)
      where
        prf : ∀ {ys}
            → ys ++ []
            ≡ ys
        prf = solve (++-monoid X)
    runFree (suc {suffix = suffix} pickMany q qs)
     -- xs
      = runPickMany pickMany
     -- input ++ suffix
      ⟫ first (runQ q) suffix
     -- output ++ suffix
      ⟫ runFree qs
     -- ys
