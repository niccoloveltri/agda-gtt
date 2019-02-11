\AgdaHide{
\begin{code}
module GTT.TypeFormers.TypeIsomorphisms where

open import Data.Product
open import Data.Sum
open import Prelude
open import GTT.Structure
open import GTT.TypeFormers.ClockQuantification public
open import GTT.TypeFormers.Force public
open import GTT.TypeFormers.FunctionType public
open import GTT.TypeFormers.Later public
open import GTT.TypeFormers.LaterType public
open import GTT.TypeFormers.ProductType public
open import GTT.TypeFormers.SumType public
open import GTT.TypeFormers.WeakenClock public

open PSh
open ■
\end{code}
}

\begin{code}
■const-tm : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm Γ (■ (⇑ A) ⇒ A)
■const-tm Γ A γ x = ■cone x ∞

module _ (Γ : SemCtx ∅) (A : SemTy κ) (B : SemTy κ) where
  sum-lem₁ : (t : ■ (A ⊕ B)) (x : Obj A ∞)
    → ■cone t ∞ ≡ inj₁ x
    → Σ (■ A) (λ s → (i : Size) → ■cone t i ≡ inj₁ (■cone s i))
  ■cone (proj₁ (sum-lem₁ t x q)) i = Mor A ∞ i x
  ■com (proj₁ (sum-lem₁ t x q)) i j = sym (MorComp A)
  proj₂ (sum-lem₁ t x q) i =
    begin
      ■cone t i
    ≡⟨ sym (■com t ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (■cone t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₁ (Mor A ∞ i x)
    ∎

  sum-lem₂ : (t : ■ (A ⊕ B)) (x : Obj B ∞)
    → ■cone t ∞ ≡ inj₂ x
    → Σ (■ B) (λ s → (i : Size) → ■cone t i ≡ inj₂ (■cone s i))
  ■cone (proj₁ (sum-lem₂ t x q)) i = Mor B ∞ i x
  ■com (proj₁ (sum-lem₂ t x q)) i j = sym (MorComp B)
  proj₂ (sum-lem₂ t x q) i =
    begin
      ■cone t i
    ≡⟨ sym (■com t ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (■cone t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₂ (Mor B ∞ i x)
    ∎

  ■sum-tm : SemTm Γ (■ (A ⊕ B) ⇒ (■ A ⊕ ■ B))
  ■sum-tm γ record { ■cone = tcone ; ■com = tcom } with tcone ∞ | inspect tcone ∞
  ... | inj₁ x | [ eq ] = inj₁ (proj₁ (sum-lem₁ (record { ■cone = tcone ; ■com = tcom }) x eq))
  ... | inj₂ y | [ eq ] = inj₂ (proj₁ (sum-lem₂ (record { ■cone = tcone ; ■com = tcom }) y eq))
\end{code}
