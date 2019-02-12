
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

-- The constant presheaf over a type A : Set
module _ (A : Set) where

  ConstObj : Size → Set
  ConstObj i = A

  ConstMor : (i : Size) (j : Size< (↑ i))
    → ConstObj i → ConstObj j
  ConstMor i j x = x

  ConstMorId : {i : Size} {x : A}
    → ConstMor i i x ≡ x
  ConstMorId = refl

  ConstMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ConstObj i}
    → ConstMor i k x ≡ ConstMor j k (ConstMor i j x)
  ConstMorComp = refl

Const : Set → PSh
Const A = record
  { Obj = ConstObj A
  ; Mor = ConstMor A
  ; MorId = ConstMorId A
  ; MorComp = ConstMorComp A
  }
