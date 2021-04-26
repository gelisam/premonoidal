open import Data.List
open import Data.List.Properties using (++-monoid)
open import Data.Product
open import Relation.Binary.PropositionalEquality

import Category.Ski
open import Tactic.MonoidSolver using (solve)


module Category.Premonoidal.Symmetric.StringDiagram
       {X : Set}
       (Q : List X → List X → Set)
       (Focusing : List X → List X → List X → Set)
       where
  data Apply : List X → List X → Set where
    apply
      : ∀ {a input output leftover}
      → Focusing a input leftover
      → Q input output
      → Apply a (output ++ leftover)

  Rearranging : List X → List X → Set
  Rearranging a b = Focusing a b []

  open Category.Ski Apply Rearranging

  StringDiagram : List X → List X → Set
  StringDiagram = Ski

  module StringDiagram-Properties
         (id-Rearranging : ∀ {a}
                         → Rearranging a a)
         (compose-Rearranging : ∀ {a b c}
                              → Rearranging a b
                              → Rearranging b c
                              → Rearranging a c)
         (widen-Rearranging : ∀ {a b}
                            → (pre : List X)
                            → Rearranging a b
                            → (post : List X)
                            → Rearranging (pre ++ a ++ post)
                                          (pre ++ b ++ post))
         (swap-Rearranging : ∀ a b
                           → Rearranging (a ++ b)
                                         (b ++ a))
         (propagate-Focusing : ∀ {a b input leftover}
                             → Rearranging a b
                             → Focusing b input leftover
                             → ∃ λ leftover′
                             → Focusing a input leftover′
                             × Rearranging leftover′ leftover)
         (widen-Focusing : ∀ {a input leftover}
                         → (pre : List X)
                         → Focusing a input leftover
                         → (post : List X)
                         → Focusing (pre ++ a ++ post)
                                    input
                                    (pre ++ leftover ++ post))
         where
    propagate-Apply
      : ∀ {a b z}
      → Rearranging a b
      → Apply b z
      → ∃ λ b′
      → Apply a b′
      × Rearranging b′ z
    propagate-Apply {a} .{b} .{output ++ leftover}
                    r-ab
                    (apply {b} {input} {output} {leftover} f-bil q)
      = let leftover′ , f-bil′ , r-l′l = propagate-Focusing r-ab f-bil

            b′ : List X
            b′ = output ++ leftover′

            z : List X
            z = output ++ leftover

            prf : ∀ xs → output ++ xs ++ [] ≡ output ++ xs
            prf _ = solve (++-monoid X)

            r-b′z : Rearranging b′ z
            r-b′z = subst (λ – → Rearranging (output ++ leftover′) –) (prf leftover)
                  ( subst (λ – → Rearranging – _) (prf leftover′)
                  ( widen-Rearranging output r-l′l []))
        in b′ , apply f-bil′ q , r-b′z

    open Ski-Properties
      id-Rearranging
      compose-Rearranging
      propagate-Apply
      public
      renaming ( id-Ski to id-StringDiagram
               ; compose-Ski to compose-StringDiagram
               )

    module _
           ( f : List X → List X)
           ( bump-Rearranging
           : ∀ {a b}
           → Rearranging a b
           → Rearranging (f a) (f b)
           )
           ( bump-Focusing
           : ∀ {a input leftover}
           → Focusing a input leftover
           → Focusing (f a) input (f leftover)
           )
           ( strong
           : ∀ a b
           → Rearranging (a ++ f b)
                         (f (a ++ b))
           )
           where
      bump-StringDiagram
        : ∀ {a z}
        → StringDiagram a z
        → StringDiagram (f a) (f z)
      bump-StringDiagram (zero r-az)
        = zero (bump-Rearranging r-az)
      bump-StringDiagram .{a} {z}
                         (suc (apply {a} {input} {output} {leftover}
                                     f-ail q)
                              s-olz)
        = let f-faifl : Focusing (f a) input (f leftover)
              f-faifl = bump-Focusing f-ail

              s-ofl-fol : StringDiagram (output ++ f leftover)
                                        (f (output ++ leftover))
              s-ofl-fol = zero (strong output leftover)

              s-fol-fz : StringDiagram (f (output ++ leftover)) (f z)
              s-fol-fz = bump-StringDiagram s-olz

              s-ofl-fz : StringDiagram (output ++ f leftover) (f z)
              s-ofl-fz = compose-StringDiagram s-ofl-fol s-fol-fz
          in suc (apply f-faifl q) s-ofl-fz

    widen-StringDiagram
      : ∀ {a z}
      → (pre : List X)
      → StringDiagram a z
      → (post : List X)
      → StringDiagram (pre ++ a ++ post)
                      (pre ++ z ++ post)
    widen-StringDiagram pre s-az post
      = bump-StringDiagram f bump-Rearranging bump-Focusing strong s-az
      where
        f : List X → List X
        f xs
          = pre ++ xs ++ post

        bump-Rearranging
          : ∀ {a b}
          → Rearranging a b
          → Rearranging (pre ++ a ++ post)
                        (pre ++ b ++ post)
        bump-Rearranging r-ab
          = widen-Rearranging pre r-ab post

        bump-Focusing
          : ∀ {a input leftover}
          → Focusing a input leftover
          → Focusing (pre ++ a ++ post)
                     input
                     (pre ++ leftover ++ post)
        bump-Focusing f-ail
          = widen-Focusing pre f-ail post

        strong
          : ∀ a b
          → Rearranging (a ++ (pre ++ b ++ post))
                        (pre ++ (a ++ b) ++ post)
        strong a b
          = subst (λ – → Rearranging – (pre ++ (a ++ b) ++ post)) prf1
          ( subst (λ – → Rearranging ([] ++ (a ++ pre) ++ (b ++ post)) –) prf2
          ( widen-Rearranging [] (swap-Rearranging a pre) (b ++ post)))
          where
            prf1
              : ([] ++ (a ++ pre) ++ (b ++ post))
              ≡ (a ++ (pre ++ b ++ post))
            prf1
              = solve (++-monoid X)

            prf2
              : ([] ++ (pre ++ a) ++ (b ++ post))
              ≡ (pre ++ (a ++ b) ++ post)
            prf2
              = solve (++-monoid X)

    swap-StringDiagram
      : ∀ a b
      → StringDiagram (a ++ b)
                      (b ++ a)
    swap-StringDiagram a b
      = zero (swap-Rearranging a b)
