module Category where

open import Relation.Binary.PropositionalEquality


postulate Object : Set
postulate Morphism : Object → Object → Set
postulate id : ∀ {a} → Morphism a a
postulate _>>>_ : ∀ {a b c} → Morphism a b → Morphism b c → Morphism a c
infixr 5 _>>>_

postulate id->>> : ∀ {a b}
                 → (f : Morphism a b)
                 → id >>> f ≡ f
postulate >>>-id : ∀ {a b}
                 → (f : Morphism a b)
                 → f >>> id ≡ f
postulate >>>->>> : ∀ {a b c d}
                  → (f : Morphism a b) → (g : Morphism b c) → (h : Morphism c d)
                  → (f >>> g) >>> h
                  ≡ f >>> (g >>> h)
