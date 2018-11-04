-- Encoding https://ncatlab.org/nlab/show/premonoidal+category#definition
module Binoidal where

open import Relation.Binary.PropositionalEquality

open import Category


-- A "binoidal" category is a category C equiped with
--   * for each pair a, b of objects of C, an object a ⊗ b
--   * for each object x, a functor x ⋊ − whose action on objects sends a to x ⊗ a
--   * for each object x, a functor − ⋉ x whose action on objects sends a to a ⊗ x
postulate _⊗_ : Object → Object → Object
postulate _⋊_ : ∀ x {a b} → Morphism a b → Morphism (x ⊗ a) (x ⊗ b)
postulate _⋉_ : ∀ {a b} → Morphism a b → ∀ x → Morphism (a ⊗ x) (b ⊗ x)
infixr 6 _⊗_
infix 6 _⋊_
infix 6 _⋉_

postulate id-⋉ : ∀ {a x}
               → id ⋉ x ≡ id {a ⊗ x}
postulate ⋊-id : ∀ {x a}
               → x ⋊ id ≡ id {x ⊗ a}
postulate ⋊->>> : ∀ {x a b c}
                  → (f : Morphism a b) → (g : Morphism b c)
                  → x ⋊ (f >>> g) ≡ x ⋊ f >>> x ⋊ g
postulate >>>-⋉ : ∀ {x a b c}
                  → (f : Morphism a b) → (g : Morphism b c)
                  → (f >>> g) ⋉ x ≡ f ⋉ x >>> g ⋉ x

-- A morphism f : a → b in a binoidal category is "central" if
-- <paraphrasing>we can slide it past any morphism g : x → y. In this
-- case, we can write < f ⊗ g > without specifying whether it is f or
-- g which executes first.</paraphrasing>
record Central {a b} (f : Morphism a b) : Set where
  field
    _-⊗ : ∀ {x y}
        → (g : Morphism x y)
        → f ⋉ _ >>> _ ⋊ g
        ≡ _ ⋊ g >>> f ⋉ _
    ⊗-_ : ∀ {x y}
        → (g : Morphism x y)
        → _ ⋊ f >>> g ⋉ _
        ≡ g ⋉ _ >>> _ ⋊ f 

<_⊗_> : ∀ {a b x y} → Morphism a b → Morphism x y → Morphism (a ⊗ x) (b ⊗ y)
< f ⊗ g > = f ⋉ _ >>> _ ⋊ g
