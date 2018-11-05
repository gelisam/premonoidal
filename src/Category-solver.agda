-- We can't use Monoid-solver because Morphism has type Object → Object → Set, not Set.
module Category-solver where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
import Data.Fin as Fin
import Data.Vec as Vec

open import Category

open ≡-Reasoning


data MorphismVec : (a b : Object) → Set where
  []  : ∀ {a} → MorphismVec a a
  _∷_ : ∀ {a b c} → Morphism a b → MorphismVec b c → MorphismVec a c

_++_ : ∀ {a b c} → MorphismVec a b → MorphismVec b c → MorphismVec a c
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

canon : ∀ {a b} → MorphismVec a b → Morphism a b
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

morphism : ∀ {a b xs} → Shape a b xs → Morphism a b
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
  example1 : ∀ {a b c}
           → {f : Morphism a b} {g : Morphism b c}
           → (id >>> f) >>> (g >>> id) ≡ f >>> id >>> g
  example1 = prove (([id] [>>>] −) [>>>] (− [>>>] [id]))
                   (− [>>>] [id] [>>>] −)


data Group : ∀ a b → MorphismVec a b → Set where
  zero : ∀ {a} → Group a a []
  suc  : ∀ {a b c xs}
       → {x : Morphism a b}
       → Group b c xs
       → Group a c (x ∷ xs)

group~>nat : ∀ {a b xs} → Group a b xs → ℕ
group~>nat zero    = zero
group~>nat (suc g) = suc (group~>nat g)

group~>shape : ∀ {a b xs} → Group a b xs → Shape a b xs
group~>shape zero       = [id]
group~>shape (suc zero) = −
group~>shape (suc g)    = − [>>>] group~>shape g

group : ∀ {a b xs}
      → {g : Group a b xs}
      → (n : ℕ)
      → group~>nat g ≡ n
      → Shape a b xs
group {g = g} _ _ = group~>shape g

private
  example2 : ∀ {a b c d e}
           → {f : Morphism a b} {g : Morphism b c} {h : Morphism c d} {i : Morphism d e}
           → f >>> g >>> h >>> i
           ≡ (f >>> g) >>> (h >>> i)
  example2 = prove (group 4 refl)
                   (group 2 refl [>>>] group 2 refl)
