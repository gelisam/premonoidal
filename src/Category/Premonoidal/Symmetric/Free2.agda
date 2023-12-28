-- Another approach to free symmetric premonoidal categories.
-- This time each 'Q' input is tied to a previous 'Q' output, a description
-- which remains more stable when two 'Free's are composed.
module Category.Premonoidal.Symmetric.Free2 where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

module _ {X : Set} where
  -- Select one element of a list.
  data Elem (px : X) : List X → Set where
    Here
      : ∀ {xs}
      → Elem px (px ∷ xs)
    There
      : ∀ {x xs}
      → Elem px xs
      → Elem px (x ∷ xs)

  -- Replace the selected element with another value.
  --
  -- >>> setElem (There Here) 0 [1, 2, 3, 4]
  -- [1, 0, 3, 4]
  setElem
    : ∀ {px xs}
    → Elem px xs
    → X
    → List X
  setElem (Here {xs}) px'
    = px' ∷ xs
  setElem (There {x} i) px'
    = x ∷ setElem i px'

  weaken-List
    : X
    → List X
    → List X
  weaken-List px xs
    = px ∷ xs

  weaken-Elem
    : ∀ {px xs}
    → Elem px xs
    → Elem px (weaken-List px xs)
  weaken-Elem i
    = There i

module _ {X : Set} where
  -- We want to use each variable exactly once. The metaphor we use is that each
  -- variable is a port, and we can only plug one wire into each port.

  -- Tracks which ports are still available, and which ones are "locked",
  -- meaning that a wire has already been plugged into that port. Could
  -- represent the list of outputs of a 'Q', or 'Free''s original list of
  -- inputs, before any 'Q' has been applied.
  --
  -- For readability, in the examples we render
  --
  -- > a ∷ (🔒∷ (c ∷ (🔒∷ (e ∷ []))))
  --
  -- as
  --
  -- > [a, 🔒, c, 🔒, e]
  data PortList : Set where
    []
      : PortList
    _∷_
      : X → PortList → PortList
    🔒∷_
      : PortList → PortList

  -- A 'PortList' where all the ports are unlocked.
  --
  -- >>> toPortList [a, b, c]
  -- [a, b, c]
  toPortList
    : List X
    → PortList
  toPortList []
    = []
  toPortList (x ∷ xs)
    = x ∷ toPortList xs

  -- List the ports which are still available.
  --
  -- >>> fromPortList [a, 🔒, c, 🔒, e]
  -- [a, c, e]
  fromPortList
    : PortList
    → List X
  fromPortList []
    = []
  fromPortList (x ∷ xs)
    = x ∷ fromPortList xs
  fromPortList (🔒∷ xs)
    = fromPortList xs

  -- Like 'Elem', but only an unlocked port can be selected.
  data PortElem (px : X) : PortList → Set where
    Here
      : ∀ {xs}
      → PortElem px (px ∷ xs)
    There
      : ∀ {x xs}
      → PortElem px xs
      → PortElem px (x ∷ xs)
    🔒There
      : ∀ {xs}
      → PortElem px xs
      → PortElem px (🔒∷ xs)

  -- Replace the selected port with a '🔒'.
  --
  -- >>> lockPortListElem {c} {[a, 🔒, c, 🔒, e]} (There (🔒There Here))
  -- [a, 🔒, 🔒, 🔒, e]
  lockPortListElem
    : ∀ {px xs}
    → PortElem px xs
    → PortList
  lockPortListElem Here
    = 🔒∷ []
  lockPortListElem (There {x} i)
    = x ∷ lockPortListElem i
  lockPortListElem (🔒There i)
    = 🔒∷ lockPortListElem i

  -- Replace every remaining port with a '🔒'.
  --
  -- >>> lockPortList [a, 🔒, c, 🔒, e]
  -- [🔒, 🔒, 🔒, 🔒, 🔒]
  lockPortList
    : PortList
    → PortList
  lockPortList []
    = []
  lockPortList (x ∷ xs)
    = 🔒∷ lockPortList xs
  lockPortList (🔒∷ xs)
    = 🔒∷ lockPortList xs

  🔒weaken-PortList
    : PortList
    → PortList
  🔒weaken-PortList xs
    = 🔒∷ xs

  🔒weaken-PortElem
    : ∀ {px xs}
    → PortElem px xs
    → PortElem px (🔒weaken-PortList xs)
  🔒weaken-PortElem i
    = 🔒There i

  🔒weaken-lockPortListElem
    : ∀ {px xs}
    → {i : PortElem px xs}
    → lockPortListElem (🔒weaken-PortElem i)
    ≡ 🔒weaken-PortList (lockPortListElem i)
  🔒weaken-lockPortListElem
    = refl

  🔒weaken-lockPortList
    : ∀ {xs}
    → lockPortList (🔒weaken-PortList xs)
    ≡ 🔒weaken-PortList (lockPortList xs)
  🔒weaken-lockPortList
    = refl

  -- Tracks all the ports, starting with 'Free''s original list of inputs,
  -- followed by the outputs of every 'Q' applied so far, in order.
  --
  -- For example, suppose 'Free' starts with inputs @a₀@, @b₀@, and @c₀@. The
  -- 'PortGrid' value at the beginning is thus:
  --
  -- > [ [a₀, b₀, c₀]
  -- > ]
  --
  -- We then apply a @Q [a₀] [a₁, b₁]@, consuming the @a₀@ and producing two new
  -- open ports:
  --
  -- > [ [🔒, b₀, c₀]
  -- > , [a₁, b₁]
  -- > ]
  --
  --
  -- We then apply a @Q [b₀, b₁] []@, consuming the @b₀@ and @b₁@ and
  -- producing no new open ports:
  --
  -- > [ [🔒, 🔒, c₀]
  -- > , [a₁, 🔒]
  -- > , []
  -- > ]
  --
  -- This composition thus results in two final output values, @c₀@ and @a₁@.
  PortGrid : Set
  PortGrid = List PortList

  -- A 'PortGrid' with only the original list of inputs, all unlocked.
  --
  -- >>> toPortGrid [a₀, b₀, c₀]
  -- [ [a₀, b₀, c₀]
  -- ]
  toPortGrid
    : List X
    → PortGrid
  toPortGrid xs
    = [ toPortList xs ]

  -- List the ports which are still available.
  --
  -- >>> fromPortGrid [ [🔒, 🔒, c₀]
  --                  , [a₁, 🔒]
  --                  ]
  -- [c₀, a₁]
  fromPortGrid
    : PortGrid
    → List X
  fromPortGrid []
    = []
  fromPortGrid (xs ∷ xss)
    = fromPortList xs ++ fromPortGrid xss

  -- Replace the selected port with a '🔒'.
  --
  -- >>> lockPortGridElem
  --       {a₁}
  --       {[a₁, 🔒]}
  --       {[ [🔒, 🔒, c₀]
  --        , [a₁, 🔒]
  --        , []
  --        ]}
  --       (There Here)  -- [a₁, 🔒] is the second row
  --       Here          -- a₁ is the first port in [a₁, 🔒]
  -- [ [🔒, 🔒, c₀]
  -- , [🔒, 🔒]
  -- , []
  -- ]
  lockPortGridElem
    : {px : X}
    → {xs : PortList}
    → {xss : PortGrid}
    → Elem xs xss
    → PortElem px xs
    → PortGrid
  lockPortGridElem i j
    = setElem i (lockPortListElem j)

  -- Replace every remaining port with a '🔒'.
  --
  -- >>> lockPortGrid [ [🔒, 🔒, c₀]
  --                  , [a₁, 🔒]
  --                  , []
  --                  ]
  -- [ [🔒, 🔒, 🔒]
  -- , [🔒, 🔒]
  -- , []
  -- ]
  lockPortGrid
    : PortGrid
    → PortGrid
  lockPortGrid []
    = []
  lockPortGrid (xs ∷ xss)
    = lockPortList xs ∷ lockPortGrid xss

  🔒weaken-PortGrid
    : PortGrid
    → PortGrid
  🔒weaken-PortGrid []
    = []
  🔒weaken-PortGrid (xs ∷ xss)
    = 🔒weaken-PortList xs ∷ xss

  🔒weaken-lockPortGridElem-Here
    : ∀ {px xs xss}
    → {j : PortElem px xs}
    → lockPortGridElem Here (🔒weaken-PortElem j)
    ≡ 🔒weaken-PortGrid (lockPortGridElem Here j)
  🔒weaken-lockPortGridElem-Here {px} {xs} {xss} {j}
    = begin
        lockPortGridElem Here (🔒weaken-PortElem j)
      ≡⟨⟩
        lockPortListElem (🔒weaken-PortElem j) ∷ xss
      ≡⟨ cong (λ — → — ∷ xss) 🔒weaken-lockPortListElem ⟩
        🔒weaken-PortList (lockPortListElem j) ∷ xss
      ≡⟨⟩
        🔒weaken-PortGrid (lockPortGridElem Here j)
      ∎

  -- Transition from one 'PortGrid' to another, by locking a number of ports.
  -- Used to select the inputs of a 'Q'.
  --
  -- For readability, in the examples we render
  --
  -- > Cons {b₀} Here (There Here)
  -- >   (Cons {b₁} (There Here) (There Here)
  -- >     Nil)
  --
  -- as
  --
  -- > [ [🔒, ⟨b₀⟩₀, c₀]
  -- > , [a₁, ⟨b₁⟩₁]
  -- > ]
  data AttachPorts (xss : PortGrid) : List X → PortGrid → Set where
    Nil
      : AttachPorts xss [] xss
    Cons
      : ∀ {px pxs xs xss'}
      → (i : Elem xs xss)
      → (j : PortElem px xs)
      → AttachPorts (lockPortGridElem i j) pxs xss'
      → AttachPorts xss (px ∷ pxs) xss'

  module _ (Q : List X → List X → Set) where
    -- A variant of 'Free' which tracks the ports which are still available at
    -- the beginning of the computation, and the wires which are still
    -- unconnected at the end of the computation.
    data FreePort (xss : PortGrid) : List X → Set where
      Nil
        : ∀ {pxs}
        → AttachPorts xss pxs []
        → FreePort xss pxs
      Cons
        : ∀ {pxs xss' ys zs}
        → AttachPorts xss pxs xss'
        → Q pxs ys
        → FreePort (xss' ++ [ toPortList ys ]) zs  -- TODO: use a snoc-list for performance
        → FreePort xss zs

    -- This module's main export: a free symmetric premonoidal category, indexed
    -- by the list of wires coming in and the list of wires coming out.
    data Free (xs : List X) (ys : List X) : Set where
      MkFree
        : FreePort [ toPortList xs ] ys
        → Free xs ys