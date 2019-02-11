\AgdaHide{
\begin{code}
module GTT.TypeFormers.UnitType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import GTT.Structure

open NatTrans
open PSh
\end{code}
}

\begin{code}
Unit : {b : ClockCtx} → SemTy b
Unit {∅} = ⊤
Unit {κ} = Terminal

⋆ : {b : ClockCtx} (Γ : SemCtx b) → SemTm Γ Unit
⋆ {∅} Γ x = tt
nat-map (⋆ {κ} Γ) i x = tt
nat-com (⋆ {κ} Γ) i j x = refl

Unit-rec : {b : ClockCtx} (Γ : SemCtx b) (A : SemTy b)
  → SemTm Γ A → SemTm (Γ ,, Unit) A
Unit-rec {∅} Γ A t x = t (proj₁ x)
nat-map (Unit-rec {κ} Γ A t) i x = nat-map t i (proj₁ x)
nat-com (Unit-rec {κ} Γ A t) i j x =
  begin
    Mor A i j (nat-map t i (proj₁ x))
  ≡⟨ nat-com t i j (proj₁ x) ⟩
    nat-map t j (proj₁ (ProdMor Γ Terminal i j x))
  ∎
\end{code}
