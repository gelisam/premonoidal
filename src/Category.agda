module Category where

open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


postulate Object : Set
postulate Morphism : Object → Object → Set
postulate id : ∀ {a} → Morphism a a
postulate _>>>_ : ∀ {a b c} → Morphism a b → Morphism b c → Morphism a c
infixr 5 _>>>_

postulate id->>> : ∀ {a b}
                 → {f : Morphism a b}
                 → id >>> f ≡ f
postulate >>>-id : ∀ {a b}
                 → {f : Morphism a b}
                 → f >>> id ≡ f
postulate >>>->>> : ∀ {a b c d}
                  → {f : Morphism a b} {g : Morphism b c} {h : Morphism c d}
                  → (f >>> g) >>> h
                  ≡ f >>> (g >>> h)

-- nicer syntax for equational reasoning
⟨>>>_⟩ : ∀ {a b c}
       → {f : Morphism a b} {g h : Morphism b c}
       → g ≡ h
       → f >>> g
       ≡ f >>> h
⟨>>>_⟩ {f = f} = cong (λ − → f >>> −)
⟨_>>>⟩ : ∀ {a b c}
       → {f g : Morphism a b} {h : Morphism b c}
       → f ≡ g
       → f >>> h
       ≡ g >>> h
⟨_>>>⟩ {h = h} = cong (λ − → − >>> h)
>>>-_ : ∀ {a b}
      → {f : Morphism a b} {g : Morphism b b}
      → g ≡ id
      → f >>> g ≡ f
>>>-_ {f = f} {g = g} prf =
  begin
    f >>> g
  ≡⟨ ⟨>>> prf ⟩ ⟩
    f >>> id
  ≡⟨ >>>-id ⟩
    f
  ∎
_->>> : ∀ {a b}
      → {f : Morphism a a} {g : Morphism a b}
      → f ≡ id
      → f >>> g ≡ g
_->>> {f = f} {g = g} prf =
  begin
    f >>> g
  ≡⟨ ⟨ prf >>>⟩ ⟩
    id >>> g
  ≡⟨ id->>> ⟩
    g
  ∎
