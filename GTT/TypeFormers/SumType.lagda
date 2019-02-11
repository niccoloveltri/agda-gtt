\AgdaHide{
\begin{code}
module GTT.TypeFormers.SumType where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Prelude
open import Presheaves
open import GTT.Structure

open PSh
open NatTrans
\end{code}
}

\begin{code}
_⊕_ : {Δ : ClockCtx} (A B : SemTy Δ) → SemTy Δ
_⊕_ {∅} A B = A ⊎ B
_⊕_ {κ} A B = Sum A B
\end{code}

\begin{code}
inl : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) (x : SemTm Γ A) → SemTm Γ (A ⊕ B)
inl {∅} Γ A B t x = inj₁ (t x)
nat-map (inl {κ} Γ A B x) Δ y = inj₁ (nat-map x Δ y)
nat-com (inl {κ}Γ A B x) Δ Δ' y = 
  begin
    inj₁ (Mor A Δ Δ' (nat-map x Δ y))
  ≡⟨ cong inj₁ (nat-com x Δ Δ' y) ⟩
    inj₁ (nat-map x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
inr : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) (x : SemTm Γ B) → SemTm Γ (A ⊕ B)
inr {∅} Γ A B t x = inj₂ (t x)
nat-map (inr {κ} Γ A B x) Δ y = inj₂ (nat-map x Δ y)
nat-com (inr {κ} Γ A B x) Δ Δ' y =
  begin
    inj₂ (Mor B Δ Δ' (nat-map x Δ y))
  ≡⟨ cong inj₂ (nat-com x Δ Δ' y) ⟩ 
    inj₂ (nat-map x Δ' (Mor Γ Δ Δ' y))
  ∎
\end{code}

\begin{code}
sum-rec : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B C : SemTy Δ)
          (left : SemTm (Γ ,, A) C) (right : SemTm (Γ ,, B) C)
          → SemTm (Γ ,, (A ⊕ B)) C
sum-rec {∅} Γ A B C left right (x , inj₁ l) = left (x , l)
sum-rec {∅} Γ A B C left right (x , inj₂ r) = right (x , r)          
nat-map (sum-rec {κ} Γ A B C left right) i (x , inj₁ l) = nat-map left i (x , l)
nat-com (sum-rec {κ} Γ A B C left right) i j (x , inj₁ l) =
  begin
    Mor C i j (nat-map left i (x , l))
  ≡⟨ nat-com left i j (x , l) ⟩
    nat-map left j (Mor Γ i j x , Mor A i j l)
  ∎ 
nat-map (sum-rec {κ} Γ A B C left right) i (x , inj₂ r) = nat-map right i (x , r)
nat-com (sum-rec {κ} Γ A B C left right) i j (x , inj₂ r) =
  begin
     Mor C i j (nat-map right i (x , r))
   ≡⟨ nat-com right i j (x , r) ⟩
     nat-map right j (Mor Γ i j x , Mor B i j r)
   ∎
\end{code}
