
module Presheaves.Presheaves where

open import Prelude

-- Presheaves over the preorder of sizes
record PSh : Set₁ where
  field
    Obj : Size → Set
    Mor : (i : Size) (j : Size< (↑ i)) → Obj i → Obj j
    MorId : {i : Size} {x : Obj i} → Mor i i x ≡ x
    MorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : Obj i}
      → Mor i k x ≡ Mor j k (Mor i j x)

