-- We can't use Monoid-solver because Morphism has type Object → Object → Set, not Set.
module Category.Solver where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
import Data.Fin as Fin
import Data.Vec as Vec

open ≡-Reasoning


module _
       (Object : Set)
       (Morphism : Object → Object → Set)
       (id : ∀ {a}
           → Morphism a a)
       (_>>>_ : ∀ {a b c}
              → Morphism a b
              → Morphism b c
              → Morphism a c)
       (let infixr 5 _>>>_; _>>>_ = _>>>_)
       (id->>> : ∀ {a b}
               → {f : Morphism a b}
               → id >>> f ≡ f)
       (>>>-id : ∀ {a b}
               → {f : Morphism a b}
               → f >>> id ≡ f)
       (>>>->>> : ∀ {a b c d}
                → {f : Morphism a b}
                  {g : Morphism b c}
                  {h : Morphism c d}
                → (f >>> g) >>> h
                ≡ f >>> (g >>> h))
       where

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


  data MorphismVec : (a b : Object) → Set where
    []  : ∀ {a}
        → MorphismVec a a
    _∷_ : ∀ {a b c}
        → Morphism a b
        → MorphismVec b c
        → MorphismVec a c

  _++_ : ∀ {a b c}
       → MorphismVec a b
       → MorphismVec b c
       → MorphismVec a c
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  canon : ∀ {a b}
        → MorphismVec a b
        → Morphism a b
  canon []       = id
  canon (x ∷ xs) = x >>> canon xs

  canon-++ : ∀ {a b c}
           → (xs : MorphismVec a b)
           → (ys : MorphismVec b c)
           → canon (xs ++ ys) ≡ canon xs >>> canon ys
  canon-++ []       ys = sym id->>>
  canon-++ (x ∷ xs) ys =
    begin
      x >>> canon (xs ++ ys)
    ≡⟨ ⟨>>> canon-++ xs ys ⟩ ⟩
      x >>> canon xs >>> canon ys
    ≡⟨ sym >>>->>> ⟩
      (x >>> canon xs) >>> canon ys
    ∎


  data Shape : ∀ a b → MorphismVec a b → Set where
    −       : ∀ {a b x} → Shape a b (x ∷ [])
    [id]    : ∀ {a} → Shape a a []
    _[>>>]_ : ∀ {a b c xs ys}
            → Shape a b xs
            → Shape b c ys
            → Shape a c (xs ++ ys)
  infixr 5 _[>>>]_

  morphism : ∀ {a b xs}
           → Shape a b xs
           → Morphism a b
  morphism (− {x = x}) = x
  morphism [id]        = id
  morphism (s [>>>] t) = morphism s >>> morphism t


  prove-canon : ∀ {a b xs}
              → (s : Shape a b xs)
              → morphism s ≡ canon xs
  prove-canon −    = sym >>>-id
  prove-canon [id] = refl
  prove-canon (_[>>>]_ {xs = []} {ys = ys} s t) =
    begin
      morphism s >>> morphism t
    ≡⟨ ⟨ prove-canon s >>>⟩ ⟩
      id >>> morphism t
    ≡⟨ id->>> ⟩
      morphism t
    ≡⟨ prove-canon t ⟩
      canon ys
    ∎
  prove-canon (_[>>>]_ {xs = x ∷ xs} {ys = ys} s t) =
    begin
      morphism s >>> morphism t
    ≡⟨ ⟨ prove-canon s >>>⟩ ⟩
      (x >>> canon xs) >>> morphism t
    ≡⟨ >>>->>> ⟩
      x >>> canon xs >>> morphism t
    ≡⟨ ⟨>>> ⟨>>> prove-canon t ⟩ ⟩ ⟩
      x >>> canon xs >>> canon ys
    ≡⟨ ⟨>>> sym (canon-++ xs ys) ⟩ ⟩
      x >>> canon (xs ++ ys)
    ∎

  prove : ∀ {a b xs}
        → (s t : Shape a b xs)
        → morphism s ≡ morphism t
  prove {xs = xs} s t =
    begin
      morphism s
    ≡⟨ prove-canon s ⟩
      canon xs
    ≡⟨ sym (prove-canon t) ⟩
      morphism t
    ∎

  private
    example : ∀ {a b c}
            → {f : Morphism a b} {g : Morphism b c}
            → (id >>> f)
              >>>
              (g >>> id)
            ≡ f
              >>>
              id
              >>>
              g
    example = prove ( ([id] [>>>] −)
                      [>>>]
                      (− [>>>] [id])
                    )
                    ( −
                      [>>>]
                      [id]
                      [>>>]
                      −
                    )
