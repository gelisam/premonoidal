import Category.Ski
open import Data.List
open import Data.List.Properties using (++-monoid)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tactic.MonoidSolver using (solve)


module Category.Premonoidal.Symmetric.StringDiagram
       {X : Set}
       (Q : List X → List X → Set)
       {Leftover : Set}
       (Focusing : List X → List X → List X → Set)
       (defocus : List X → List X → List X)
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

    swap-StringDiagram
      : ∀ a b
      → StringDiagram (a ++ b)
                      (b ++ a)
    swap-StringDiagram a b
      = zero (swap-Rearranging a b)

    widen-StringDiagram
      : ∀ {a z}
      → (pre : List X)
      → StringDiagram a z
      → (post : List X)
      → StringDiagram (pre ++ a ++ post)
                      (pre ++ z ++ post)
    widen-StringDiagram pre (zero r-az) post
      = zero (widen-Rearranging pre r-az post)
    widen-StringDiagram pre
                        (suc .{a} .{output ++ leftover} {z}
                             (apply {a} {input} {output} {leftover}
                                    f-ail
                                    q)
                             s-olz)
                        post
      = let f-pap-i-plp : Focusing (pre ++ a ++ post)
                                   input
                                   (pre ++ leftover ++ post)
            f-pap-i-plp
              = widen-Focusing pre f-ail post

            a-pap-oplp : Apply (pre ++ a ++ post)
                               (output ++ pre ++ leftover ++ post)
            a-pap-oplp
              = apply f-pap-i-plp q

            prf1 : pre ++ (output ++ leftover) ++ post
                 ≡ pre ++ output ++ leftover ++ post
            prf1 = solve (++-monoid X)

            s-polp-pzp : StringDiagram (pre ++ output ++ leftover ++ post)
                                       (pre ++ z ++ post)
            s-polp-pzp
              = subst (λ – → StringDiagram – _) prf1
                  (widen-StringDiagram pre s-olz post)

            r-op-po : Rearranging (output ++ pre)
                                  (pre ++ output)
            r-op-po
              = swap-Rearranging output pre

            prf2 : (output ++ pre) ++ leftover ++ post
                 ≡ output ++ pre ++ leftover ++ post
            prf2 = solve (++-monoid X)

            prf3 : (pre ++ output) ++ leftover ++ post
                 ≡ pre ++ output ++ leftover ++ post
            prf3 = solve (++-monoid X)

            r-oplp-polp : Rearranging (output ++ pre ++ leftover ++ post)
                                      (pre ++ output ++ leftover ++ post)
            r-oplp-polp
              = subst (λ – → Rearranging – (pre ++ output ++ leftover ++ post)) prf2
              ( subst (λ – → Rearranging ((output ++ pre) ++ leftover ++ post) –) prf3
              ( widen-Rearranging [] r-op-po (leftover ++ post)))

            s-oplp-polp : StringDiagram (output ++ pre ++ leftover ++ post)
                                        (pre ++ output ++ leftover ++ post)
            s-oplp-polp
              = zero r-oplp-polp

            s-oplp-pzp : StringDiagram (output ++ pre ++ leftover ++ post)
                                       (pre ++ z ++ post)
            s-oplp-pzp
              = compose-StringDiagram s-oplp-polp s-polp-pzp

            s-pap-pzp : StringDiagram (pre ++ a ++ post)
                                      (pre ++ z ++ post)
            s-pap-pzp
              = suc a-pap-oplp s-oplp-pzp
        in s-pap-pzp
