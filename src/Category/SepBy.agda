module Category.SepBy
       {A : Set}
       (Outer Inner Final : A → A → Set)
       where

open import Data.Product


data SepBy : A → A → Set where
  zero
    : ∀ {a b}
    → Final a b
    → SepBy a b
  suc
    : ∀ {a b c d}
    → Outer a b
    → Inner b c
    → SepBy c d
    → SepBy a d

module SepBy-Properties
       (id-Final : ∀ {a}
                 → Final a a)
       (compose-Final : ∀ {a b c}
                      → Final a b
                      → Final b c
                      → Final a c)
       (propagate : ∀ {a b c d}
                  → Final a b
                  → Outer b c
                  → Inner c d
                  → ∃ λ b′
                  → ∃ λ c′
                  → Outer a b′
                  × Inner b′ c′
                  × Final c′ d)
       where
  id-SepBy
    : ∀ {a}
    → SepBy a a
  id-SepBy
    = zero id-Final

  compose-SepBy
    : ∀ {a b z}
    → SepBy a b
    → SepBy b z
    → SepBy a z
  compose-SepBy (zero f-ab) (zero f-bz)
    = zero (compose-Final f-ab f-bz)
  compose-SepBy (zero f-ab) (suc o-bc i-cd s-dz)
    = let _ , _ , o-ab′ , i-b′c′ , f-c′d = propagate f-ab o-bc i-cd
      in suc o-ab′ i-b′c′ (compose-SepBy (zero f-c′d) s-dz)
  compose-SepBy (suc o-ab i-bc s-cd) s-dz
    = suc o-ab i-bc (compose-SepBy s-cd s-dz)

  module _
         {R : A → A → Set}
         (compose-R : ∀ {a b c}
                    → R a b
                    → R b c
                    → R a c)
         (let infixr 5 _⟫_; _⟫_ = compose-R)
         (runOuter : ∀ {a b}
                   → Outer a b
                   → R a b)
         (runInner : ∀ {a b}
                   → Inner a b
                   → R a b)
         (runFinal : ∀ {a b}
                   → Final a b
                   → R a b)
         where
    runSepBy
      : ∀ {a z}
      → SepBy a z
      → R a z
    runSepBy (zero f-az)
      = runFinal f-az
    runSepBy (suc o-ab i-bc s-cz)
      = runOuter o-ab
      ⟫ runInner i-bc
      ⟫ runSepBy s-cz
