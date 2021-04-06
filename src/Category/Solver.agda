-- Yet another technique for generating proofs in Agda (in addition to the ones
-- I've described in https://gist.github.com/gelisam/486d4992c0f3a3f3da2f58ff0e1a3e72):
-- transform the proposition into a simpler one which can be proved using refl.
--
-- This is the approach I use in my https://github.com/agda/agda-finite-prover
-- package, which can prove equations universally-quantified over finite types,
-- e.g. proving the commutativity of the boolean function '∧'. I simplify the
-- proposition to a long enumeration of all the concrete cases, each of which
-- can be proved using refl:
--
--       false ∧ false ≡ false ∧ false
--     × false ∧ true  ≡ true  ∧ false
--     × true  ∧ false ≡ false ∧ true
--     × true  ∧ true  ≡ true  ∧ true
--
-- This is also the approach used by Tactic.MonoidSolver in the standard library
-- (https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda),
-- which can prove monoid expresions equivalent if they only differ by the
-- placement of the parentheses and the presence of identity elements, e.g.
--
--     (0 + x) + (y + 0) ≡ x + 0 + y
--
-- It simplifies both sides to their normal form, resulting in a simple
-- proposition which can be proved using refl:
--
--     x + (y + 0) ≡ x + (y + 0)
--
-- In this file, I reimplement the Tactic.MonoidSolver idea, but instead of
-- using a monoid with an associative operation and an identity element, I use
-- a category, where morphism composition is associative and every object has
-- an identity element. That is, I'll be proving
--
--     (id >>> f) >>> (g >>> id) ≡ f >>> id >>> g
--
-- by rewriting both sides to their normal form:
--
--     f >>> (g >>> id) ≡ f >>> (g >>> id)
--
-- and then asking the user to provide the easy refl proof of that simplified
-- equation. In order to convert this proof into a proof of the original
-- equation, we'll need to generate a proof that each side is equal to its
-- simplified form.
module Category.Solver where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
import Data.Fin as Fin
import Data.Vec as Vec

open ≡-Reasoning


-- The algorithm is parameterized over an arbitrary category, so we ask the
-- user to specify objects, morphisms, identity morphisms, and morphism
-- composition. We also ask the user to prove that the identity morphism is an
-- identity for morphism composition, and that morphism composition is
-- associative.
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

  -- In Agda, the syntax for applying a proof (x≡y : x ≡ y) to prove that
  -- (x + z) ≡ (y + z) looks like this:
  --
  --     begin
  --       x + z
  --     ≡⟨ cong (λ – → – + z) x≡y ⟩
  --       y + z
  --     ∎
  --
  -- cong asks for a function specifying where we want to apply our proof. I
  -- find its API a bit too verbose; I would prefer to put the proof x≡y where
  -- the – is. So I define wrappers for all my binary operators, this way I can
  -- write this instead:
  --
  --     begin
  --       x + z
  --     ≡⟨ ⟨ x≡y +⟩ ⟩
  --       y + z
  --     ∎
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


  -- We'll need to be able to pattern-match on the canonical representation
  -- (f >>> g >>> id). We can't do that if we represent it using a value of
  -- type Morphism, because the user might have instantiated Morphism to an
  -- opaque type such as _→_. So we instead represent it as (f ∷ g ∷ []), a
  -- list-like value which enforces that consecutive morphisms have compatible
  -- types...
  data Canon : Object → Object → Set where
    []  : ∀ {a}
        → Canon a a
    _∷_ : ∀ {a b c}
        → Morphism a b
        → Canon b c
        → Canon a c

  -- ...and which can easily be converted to (f >>> (g >>> id)) when needed.
  runCanon : ∀ {a b}
           → Canon a b
           → Morphism a b
  runCanon []       = id
  runCanon (f ∷ fs) = f >>> runCanon fs

  -- One big advantage of this representation is that it is composable.
  -- With Morphism, even though (f >>> (g >>> id)) and (h >>> id) are both in
  -- canonical form, their composition (f >>> (g >>> id)) >>> (h >>> id) is
  -- not. With the Canon representations (f ∷ g ∷ []) and (h ∷ []), we can
  -- easily obtain the composition (f ∷ g ∷ h ∷ []) using list-concatenation.
  -- Which we can now easily implement using pattern-matching.
  _++_ : ∀ {a b c}
       → Canon a b
       → Canon b c
       → Canon a c
  []       ++ gs = gs
  (f ∷ fs) ++ gs = f ∷ (fs ++ gs)

  -- Note that while (f >>> (g >>> id)) >>> (h >>> id) is not canonical, the
  -- associativity and identity laws we have assumed for _>>>_ allow us to
  -- conclude that (f >>> (g >>> id)) >>> (h >>> id) is equal to the canonical
  -- representation (f >>> (g >>> (h >>> id))), a.k.a. runCanon [f ∷ g ∷ h ∷ id].
  -- This will be very helpful in a moment when we prove that each side is
  -- equal to its canonical form.
  runCanon-++ : ∀ {a b c}
              → (fs : Canon a b)
              → (gs : Canon b c)
              → runCanon (fs ++ gs) ≡ runCanon fs >>> runCanon gs
  runCanon-++ [] gs =
    begin
      runCanon ([] ++ gs)
    ≡⟨⟩
      runCanon gs
    ≡⟨ sym id->>> ⟩
      id >>> runCanon gs
    ≡⟨⟩
      runCanon [] >>> runCanon gs
    ∎
  runCanon-++ (f ∷ fs) gs =
    begin
      runCanon ((f ∷ fs) ++ gs)
    ≡⟨⟩
      runCanon (f ∷ (fs ++ gs))
    ≡⟨⟩
      f >>> runCanon (fs ++ gs)
    ≡⟨ ⟨>>> runCanon-++ fs gs ⟩ ⟩
      f >>> (runCanon fs >>> runCanon gs)
    ≡⟨ sym >>>->>> ⟩
      (f >>> runCanon fs) >>> runCanon gs
    ≡⟨⟩
      runCanon (f ∷ fs) >>> runCanon gs
    ∎


  -- We once again have to define a data type so we can pattern-match on it.
  -- This time, it's so we can match on the two sides of the potential equality
  -- we want to prove:
  --
  --     (id >>> f) >>> (g >>> id) ≡ f >>> id >>> g
  --
  -- will be represented as
  --
  --     ([id] [>>>] [ f ]) [>>>] ([ g ] [>>>] [id])
  --
  -- and
  --
  --     [ f ] [>>>] [id] [>>>] [ g ]
  data Expr : Object → Object → Set where
    [_]     : ∀ {a b}
            → Morphism a b
            → Expr a b
    [id]    : ∀ {a}
            → Expr a a
    _[>>>]_ : ∀ {a b c}
            → Expr a b
            → Expr b c
            → Expr a c
  infixr 5 _[>>>]_

  -- Of course, we can easily convert
  --
  --     ([id] [>>>] [ f ]) [>>>] ([ g ] [>>>] [id])
  --
  -- to
  --
  --     (id >>> f) >>> (g >>> id)
  --
  -- when needed.
  runExpr : ∀ {a b}
          → Expr a b
          → Morphism a b
  runExpr [ f ]         = f
  runExpr [id]          = id
  runExpr (e₁ [>>>] e₂) = runExpr e₁ >>> runExpr e₂


  -- We are finally ready to simplify each side to its canonical form:
  --
  --     [ f ] [>>>] [id] [>>>] [ g ]
  --
  -- becomes
  --
  --     f ∷ g ∷ []
  canon : ∀ {a b} → Expr a b → Canon a b
  canon [ f ]         = f ∷ []
  canon [id]          = []
  canon (e₁ [>>>] e₂) = canon e₁ ++ canon e₂

  -- That is, (f >>> id >>> g) becomes (f >>> (g >>> id)). We are now ready to
  -- show that those that those two expressions are equivalent; that is, that
  -- each side is equal to its canonical form.
  runExpr≡runCanon : ∀ {a b}
                   → (e : Expr a b)
                   → runExpr e ≡ runCanon (canon e)
  runExpr≡runCanon [ f ] =
    begin
      runExpr [ f ]
    ≡⟨⟩
      f
    ≡⟨ sym >>>-id ⟩
      f >>> id
    ≡⟨⟩
      runCanon (f ∷ [])
    ≡⟨⟩
      runCanon (canon [ f ])
    ∎
  runExpr≡runCanon [id] =
    begin
      runExpr [id]
    ≡⟨⟩
      id
    ≡⟨⟩
      runCanon []
    ≡⟨⟩
      runCanon (canon [id])
    ∎
  runExpr≡runCanon (e₁ [>>>] e₂) =
    begin
      runExpr (e₁ [>>>] e₂)
    ≡⟨⟩
      runExpr e₁ >>> runExpr e₂
    ≡⟨ ⟨ runExpr≡runCanon e₁ >>>⟩ ⟩
      runCanon (canon e₁) >>> runExpr e₂
    ≡⟨ ⟨>>> runExpr≡runCanon e₂ ⟩ ⟩
      runCanon (canon e₁) >>> runCanon (canon e₂)
    ≡⟨ sym (runCanon-++ (canon e₁) (canon e₂)) ⟩
      runCanon (canon e₁ ++ canon e₂)
    ≡⟨⟩
      runCanon (canon (e₁ [>>>] e₂))
    ∎

  -- Now that all the pieces are in place, we provide the user with a magic
  -- function which automatically proves two Morphism expressions equal, for
  -- the low-low cost of repeating the expressions in Expr form, and providing
  -- the easy refl proof that the canonical representations are equal.
  prove : ∀ {a b}
        → (e₁ e₂ : Expr a b)
        → canon e₁ ≡ canon e₂
        → runExpr e₁ ≡ runExpr e₂
  prove e₁ e₂ canon₁≡canon₂ =
    begin
      runExpr e₁
    ≡⟨ runExpr≡runCanon e₁ ⟩
      runCanon (canon e₁)
    ≡⟨ cong runCanon canon₁≡canon₂ ⟩
      runCanon (canon e₂)
    ≡⟨ sym (runExpr≡runCanon e₂) ⟩
      runExpr e₂
    ∎

  -- For comparison, here's a proof written by hand:
  long-example : ∀ {a b c}
               → (f : Morphism a b) (g : Morphism b c)
               → (id >>> f) >>> (g >>> id)
               ≡ f >>> id >>> g
  long-example f g =
    begin
      (id >>> f) >>> (g >>> id)
    ≡⟨ ⟨ id->>> >>>⟩ ⟩
      f >>> (g >>> id)
    ≡⟨ ⟨>>> >>>-id ⟩ ⟩
      f >>> g
    ≡⟨ ⟨>>> sym id->>> ⟩ ⟩
      f >>> (id >>> g)
    ∎

  -- Here's the corresponding proof using our solver:
  short-example : ∀ {a b c}
                → (f : Morphism a b) (g : Morphism b c)
                → (id >>> f) >>> (g >>> id)
                ≡ f >>> id >>> g
  short-example f g = prove (([id] [>>>] [ f ]) [>>>] ([ g ] [>>>] [id]))
                            ([ f ] [>>>] [id] [>>>] [ g ])
                            refl

  -- And of course, using the "type-aware macro" technique I described in
  -- https://gist.github.com/gelisam/486d4992c0f3a3f3da2f58ff0e1a3e72, we can
  -- easily generate the Expr (and the refl) arguments from the equation we
  -- want to prove, this way we don't have to write it twice:
  --
  --     shortest-example : ∀ {a b c}
  --                      → (f : Morphism a b) (g : Morphism b c)
  --                      → (id >>> f) >>> (g >>> id)
  --                      ≡ f >>> id >>> g
  --     shortest-example f g = proveAuto
