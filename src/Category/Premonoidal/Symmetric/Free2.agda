-- Another approach to free symmetric premonoidal categories.
-- This time each 'Q' input is tied to a previous 'Q' output, a description
-- which remains more stable when two 'Free's are composed.
module Category.Premonoidal.Symmetric.Free2 where

open import Data.Nat
open import Data.List


-- Select one element of a list.
data Elem {X : Set} (x : X) : List X → Set where
  Here
    : ∀ {xs}
    → Elem x (x ∷ xs)
  There
    : ∀ {x₀ xs}
    → Elem x xs
    → Elem x (x₀ ∷ xs)

-- Replace the selected element with another value.
setElem
  : ∀ {X x xs}
  → Elem x xs
  → X
  → List X
setElem {xs = xs} Here x'
  = x' ∷ xs
setElem {xs = xs} (There {x₀} i) x'
  = x₀ ∷ setElem i x'

module _ (X : Set) where
  -- We want to use each variable exactly once. The metaphor we use is that each
  -- variable is a port, and we can only plug one wire into each port.

  -- Tracks which ports are still available, and which ones are "locked",
  -- meaning that a wire has already been plugged into that port. Could
  -- represent the list of outputs of a 'Q', or 'Free''s original list of
  -- inputs, before any 'Q' has been applied.
  data PortList : Set where
    []
      : PortList
    _∷_
      : X → PortList → PortList
    🔒∷_
      : PortList → PortList
  
  -- A 'PortList' where all the ports are unlocked.
  toPortList
    : List X
    → PortList
  toPortList []
    = []
  toPortList (x ∷ xs)
    = x ∷ toPortList xs
  
  -- Like 'Elem', but only an unlocked port can be selected.
  data PortElem (x : X) : PortList → Set where
    Here
      : ∀ {xs}
      → PortElem x (x ∷ xs)
    🔓There
      : ∀ {x₀ xs}
      → PortElem x xs
      → PortElem x (x₀ ∷ xs)
    🔒There
      : ∀ {xs}
      → PortElem x xs
      → PortElem x (🔒∷ xs)

  -- Replace the selected port with a '🔒'.
  lockPortElem
    : ∀ {x xs}
    → PortElem x xs
    → PortList
  lockPortElem Here
    = 🔒∷ []
  lockPortElem (🔓There {x₀} i)
    = x₀ ∷ lockPortElem i
  lockPortElem (🔒There {xs} i)
    = 🔒∷ xs

  -- Tracks all the ports, starting with 'Free''s original list of inputs,
  -- followed by the outputs of every 'Q' applied so far, in order.
  OpenPorts : Set
  OpenPorts = List PortList

  -- Replace the selected port with a '🔒'.
  lockOpenPortsElem
    : {x : X}
    → {xs : PortList}
    → {xss : List PortList}
    → Elem xs xss
    → PortElem x xs
    → OpenPorts
  lockOpenPortsElem i j
    = setElem i (lockPortElem j)

  -- Attach a number of wires to a number of open ports, resulting in a smaller
  -- number of ports remaining open. Used to select the inputs of a 'Q'.
  data AttachPorts (xss : OpenPorts) : List X → OpenPorts → Set where
    Nil
      : AttachPorts xss [] xss
    Cons
      : ∀ {px xs pxs xss'}
      → (i : Elem xs xss)
      → (j : PortElem px xs)
      → AttachPorts (lockOpenPortsElem i j) pxs xss'
      → AttachPorts xss (px ∷ pxs) xss'

  module _ (Q : List X → List X → Set) where
    -- A variant of 'Free' which tracks the ports which are still available at
    -- the beginning of the computation, and the wires which are still
    -- unconnected at the end of the computation.
    data FreePort (xss : OpenPorts) : List X → Set where
      Nil
        : ∀ {pxs xss'}
        → AttachPorts xss pxs []
        → FreePort xss pxs
      Cons
        : ∀ {pxs xss' ys zs}
        → AttachPorts xss pxs xss'
        → Q pxs ys
        → FreePort (xss' ++ [ toPortList ys ]) zs
        → FreePort xss zs

    -- This module's main export: a free symmetric premonoidal category, indexed
    -- by the list of wires coming in and the list of wires coming out.
    data Free (xs : List X) (ys : List X) : Set where
      MkFree
        : FreePort [ toPortList xs ] ys
        → Free xs ys