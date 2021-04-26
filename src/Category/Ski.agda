-- Like a Free Category (a list of compatible morphisms), but with a twist at the end.
module Category.Ski
       {A : Set}
       (Q Final : A → A → Set)
       where

open import Data.Product


data Ski : A → A → Set where
  zero
    : ∀ {a b}
    → Final a b
    → Ski a b
  suc
    : ∀ {a b c}
    → Q a b
    → Ski b c
    → Ski a c

module Ski-Properties
       (id-Final : ∀ {a}
                 → Final a a)
       (compose-Final : ∀ {a b c}
                      → Final a b
                      → Final b c
                      → Final a c)
       (propagate-Q : ∀ {a b c}
                    → Final a b
                    → Q b c
                    → ∃ λ b′
                    → Q a b′
                    × Final b′ c)
       where
  private
    propagate-Ski
      : ∀ {a b z}
      → Final a b
      → Ski b z
      → Ski a z
    propagate-Ski f-ab (zero f-bz)
      = zero (compose-Final f-ab f-bz)
    propagate-Ski f-ab (suc q-bc s-cz)
      = let _ , q-ab′ , f-b′c = propagate-Q f-ab q-bc
        in suc q-ab′ (propagate-Ski f-b′c s-cz)

  id-Ski
    : ∀ {a}
    → Ski a a
  id-Ski
    = zero id-Final

  compose-Ski
    : ∀ {a b z}
    → Ski a b
    → Ski b z
    → Ski a z
  compose-Ski (zero f-ab) s-bz
    = propagate-Ski f-ab s-bz
  compose-Ski (suc q-ab s-bc) s-cz
    = suc q-ab (compose-Ski s-bc s-cz)

  module _
         {R : A → A → Set}
         (compose-R : ∀ {a b c}
                    → R a b
                    → R b c
                    → R a c)
         (let infixr 5 _⟫_; _⟫_ = compose-R)
         (runQ : ∀ {a b}
               → Q a b
               → R a b)
         (runFinal : ∀ {a b}
                   → Final a b
                   → R a b)
         where
    runSki
      : ∀ {a z}
      → Ski a z
      → R a z
    runSki (zero f-az)
      = runFinal f-az
    runSki (suc q-ab s-cz)
      = runQ q-ab
      ⟫ runSki s-cz
