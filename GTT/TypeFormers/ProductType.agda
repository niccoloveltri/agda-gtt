
module GTT.TypeFormers.ProductType where

open import Data.Product
open import Data.Unit
open import Prelude
open import Presheaves
open import GTT.Structure

open PSh
open NatTrans

-- Semantic product types
_⊗_ : {Δ : ClockCtx} (A B : SemTy Δ) → SemTy Δ
_⊗_ {∅} A B = A × B
_⊗_ {κ} A B = Prod A B

-- Interpretation of the term constructors "[_&_]"
pair : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) (x : SemTm Γ A) (y : SemTm Γ B)
  → SemTm Γ (A ⊗ B)
pair {∅} Γ A B x y t = x t , y t
nat-map (pair {κ} Γ A B x y) i t = (nat-map x i t) , (nat-map y i t)
nat-com (pair {κ} Γ A B x y) i j t =
  begin
    (Mor A i j (nat-map x i t) , Mor B i j (nat-map y i t))
  ≡⟨ cong (λ z → (z , _)) (nat-com x i j t) ⟩
    (nat-map x j (Mor Γ i j t) , Mor B i j (nat-map y i t))
  ≡⟨ cong (λ z → (_ , z)) (nat-com y i j t) ⟩
    (nat-map x j (Mor Γ i j t) , nat-map y j (Mor Γ i j t))
  ∎

-- Interpretation of the term constructors "π₁"
pr₁ : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) → SemTm Γ (A ⊗ B) → SemTm Γ A
pr₁ {∅} Γ A B x t = proj₁ (x t)
nat-map (pr₁ {κ} Γ A B x) i t = proj₁ (nat-map x i t)
nat-com (pr₁ {κ} Γ A B x) i j t =
  begin
    Mor A i j (proj₁ (nat-map x i t))
  ≡⟨ cong proj₁ (nat-com x i j t) ⟩
    proj₁ (nat-map x j (Mor Γ i j t))
  ∎

-- Interpretation of the term constructors "π₂"
pr₂ : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) → SemTm Γ (A ⊗ B) → SemTm Γ B
pr₂ {∅} Γ A B x t = proj₂ (x t)
nat-map (pr₂ {κ} Γ A B x) i t = proj₂ (nat-map x i t)
nat-com (pr₂ {κ} Γ A B x) i j t =
  begin
    Mor B i j (proj₂ (nat-map x i t))
  ≡⟨ cong proj₂ (nat-com x i j t) ⟩
    proj₂ (nat-map x j (Mor Γ i j t))
  ∎
