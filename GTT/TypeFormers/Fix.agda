module GTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure
open import GTT.TypeFormers.Later
open import GTT.TypeFormers.LaterApplicative
open import GTT.TypeFormers.FunctionType

open PSh
open ►Obj
open ExpObj
open NatTrans

-- Auxiliary definition used in the construction of the semantic delayed fixpoint operation.
-- Notice that this definition is accepted by Agda's termination checker for three reasons:
-- -- 1) every recursive call is applied to a strictly smaller size;
-- -- 2) the usage of SizeLt in place of Size< in the definition of Later prevents indefinite unfolding;
-- -- 3) the usage of elimLt in the definition of LaterLim, which also prevents indefinite unfolding.
sem-dfix₁ : (A : SemTy κ) (i : Size) → ExpObj (► A) A i → ►Obj A i
►cone (sem-dfix₁ A i f) [ j ] = fun f j (sem-dfix₁ A j f)
►com (sem-dfix₁ A i f) [ j ] [ k ] =
  begin
    Mor A j k (fun f j (sem-dfix₁ A j f))
  ≡⟨ funcom f j k (sem-dfix₁ A j f) ⟩
    fun f k (►Mor A j k (sem-dfix₁ A j f))
  ≡⟨ cong (fun f k) (►eq (λ {_ → refl})) ⟩
    fun f k (sem-dfix₁ A k f)
  ∎

-- Semantic delayed fixpoint combinator, interpretation of "dfix"
sem-dfix : (Γ : SemCtx κ) (A : SemTy κ) (f : SemTm Γ (► A ⇒ A)) → SemTm Γ (► A)
nat-map (sem-dfix Γ A f) i γ = sem-dfix₁ A i (nat-map f i γ)
nat-com (sem-dfix Γ A f) i j γ = ►eq (λ {k → cong (λ a → fun a k (sem-dfix₁ A k a)) (nat-com f i j γ)})

-- Semantic fixpoint combinator
sem-fix : (Γ : SemCtx κ) (A : SemTy κ) (f : SemTm Γ (► A ⇒ A)) → SemTm Γ A
sem-fix Γ A f = sem-app-map Γ (► A) A f (sem-dfix Γ A f)

