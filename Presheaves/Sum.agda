
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

open PSh

-- Coproduct of presheaves
module _ (P Q : PSh) where

  SumObj : Size → Set
  SumObj i = Obj P i ⊎ Obj Q i

  SumMor : (i : Size) (j : Size< (↑ i))
    → SumObj i → SumObj j
  SumMor i j = map (Mor P i j) (Mor Q i j)

  SumMorId : {i : Size} {x : SumObj i}
    → SumMor i i x ≡ x
  SumMorId {i} {inj₁ p} =
    begin
      inj₁ (Mor P i i p)
    ≡⟨ cong inj₁ (MorId P) ⟩
      inj₁ p
    ∎
  SumMorId {i} {inj₂ q} =
    begin
      inj₂ (Mor Q i i q)
    ≡⟨ cong inj₂ (MorId Q) ⟩
      inj₂ q
    ∎

  SumMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : SumObj i}
    → SumMor i k x ≡ SumMor j k (SumMor i j x)
  SumMorComp {i} {j} {k} {inj₁ p} =
    begin
      inj₁ (Mor P i k p)
    ≡⟨ cong inj₁ (MorComp P) ⟩
      inj₁ (Mor P j k (Mor P i j p))
    ∎
  SumMorComp {i} {j} {k} {inj₂ q} =
    begin
      inj₂ (Mor Q i k q)
    ≡⟨ cong inj₂ (MorComp Q) ⟩
      inj₂ (Mor Q j k (Mor Q i j q))
    ∎

Sum : PSh → PSh → PSh
Sum P Q = record
  { Obj = SumObj P Q
  ; Mor = SumMor P Q
  ; MorId = SumMorId P Q
  ; MorComp = λ {_}{_}{_}{x} → SumMorComp P Q {x = x}
  }

