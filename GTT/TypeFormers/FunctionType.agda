
module GTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import GTT.Structure

open PSh
open ExpObj
open NatTrans

-- Semantic function spaces
_⇒_ : ∀ {Δ} (A B : SemTy Δ) → SemTy Δ
_⇒_ {∅} A B = A → B
_⇒_ {κ} A B = Exp A B

-- Interpretation of lambda and app
sem-lambda : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) (t : SemTm (Γ ,, A) B)
  → SemTm Γ (A ⇒ B)
sem-lambda {∅} Γ A B t x y = t (x , y)
fun (nat-map (sem-lambda {κ} Γ A B t) i x) j z = nat-map t j (Mor Γ i j x , z)
funcom (nat-map (sem-lambda {κ} Γ A B t) i x) j k z =
  begin
    Mor B j k (nat-map t j (Mor Γ i j x , z))
  ≡⟨ nat-com t j k (Mor Γ i j x , z) ⟩
    nat-map t k (Mor (Γ ,, A) j k (Mor Γ i j x , z))
  ≡⟨ cong (λ z → nat-map t k (z , _)) (sym (MorComp Γ)) ⟩
    nat-map t k (Mor Γ i k x , Mor A j k z)
  ∎
nat-com (sem-lambda {κ} Γ A B t) i j x = funeq (λ k z → cong (λ z → nat-map t k (z , _)) (MorComp Γ))

sem-app : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ)
      (f : SemTm Γ (A ⇒ B))
  → SemTm (Γ ,, A) B
sem-app {∅} Γ A B f (x , y) = f x y
nat-map (sem-app {κ} Γ A B f) i (x , y) = fun (nat-map f i x) i y
nat-com (sem-app {κ} Γ A B f) i j (x , y) =
  begin
    Mor B i j (fun (nat-map f i x) i y)
  ≡⟨ funcom (nat-map f i x) i j y ⟩
    fun (nat-map f i x) j (Mor A i j y)
  ≡⟨ cong (λ z → fun z j (Mor A i j y)) (nat-com f i j x) ⟩
    fun (nat-map f j (Mor Γ i j x)) j (Mor A i j y)
  ∎

-- Semantic version of the derived application "$"
sem-app-map : {Δ : ClockCtx} (Γ : SemCtx Δ) (A B : SemTy Δ) → SemTm Γ (A ⇒ B) → SemTm Γ A → SemTm Γ B
sem-app-map Γ A B f t = sem-sub Γ (Γ ,, A) B (sem-app Γ A B f) (sem-subst-tm Γ Γ A (sem-idsub Γ) t)

