\AgdaHide{
\begin{code}
module GTT.Structure.Subst where

open import Data.Unit
open import Data.Product
open import Prelude
open import GTT.Structure.Contexts
open import GTT.Structure.ContextOperations
open import GTT.Structure.Types
open import GTT.Structure.Terms

open PSh
open NatTrans
\end{code}
}

Since \GTT\ is a type theory with explicit substitutions, we must provide an interpretation for them as well.
Semantic substitutions are maps between contexts and we define the type \F{SemSub} in the same way as \F{SemTm}.
Definitional equality of semantic terms and substitutions is modeled as propositional equality.
\AgdaHide{
\begin{code}
SemSub : {Δ : ClockCtx} → SemCtx Δ → SemCtx Δ → Set
SemSub {∅} Γ₁ Γ₂ = Γ₁ → Γ₂
SemSub {κ} Γ₁ Γ₂ = NatTrans Γ₁ Γ₂
\end{code}
}

\AgdaHide{
As an example, we show how an explicit substitution gives rise to an actual one.
We only give the component map and not the proof of naturality.

\begin{code}
sem-sub : {Δ : ClockCtx} (Γ₁ Γ₂ : SemCtx Δ) (A : SemTy Δ)
  → SemTm Γ₂ A → SemSub Γ₁ Γ₂ → SemTm Γ₁ A
sem-sub {∅} Γ₁ Γ₂ A t α x = t(α x)
nat-map (sem-sub {κ} Γ₁ Γ₂ A t α) i x = nat-map t i (nat-map α i x)
\end{code}
\begin{code}
nat-com (sem-sub {κ} Γ₁ Γ₂ A t α) i j x =
  begin
    Mor A i j (nat-map t i (nat-map α i x))
  ≡⟨ nat-com t i j (nat-map α i x) ⟩
    nat-map t j (Mor Γ₂ i j (nat-map α i x))
  ≡⟨ cong (nat-map t j) (nat-com α i j x) ⟩
    nat-map t j (nat-map α j (Mor Γ₁ i j x))
  ∎
\end{code}
}

\AgdaHide{
\begin{code}
sem-idsub : {Δ : ClockCtx} (Γ : SemCtx Δ) → SemSub Γ Γ
sem-idsub {∅} Γ x = x
nat-map (sem-idsub {κ} Γ) i x = x
nat-com (sem-idsub {κ} Γ) i j x = refl
\end{code}

\begin{code}
sem-ε : {Δ : ClockCtx} (Γ : SemCtx Δ) → SemSub Γ (∙ Δ)
sem-ε {∅} Γ x = tt
nat-map (sem-ε {κ} Γ) i x = tt
nat-com (sem-ε {κ} Γ) i j x = refl
\end{code}

\begin{code}
sem-subcomp : {Δ : ClockCtx} (Γ₁ Γ₂ Γ₃ : SemCtx Δ) → SemSub Γ₂ Γ₃ → SemSub Γ₁ Γ₂ → SemSub Γ₁ Γ₃
sem-subcomp {∅} Γ₁ Γ₂ Γ₃ α β x = α(β x)
nat-map (sem-subcomp {κ} Γ₁ Γ₂ Γ₃ α β) i x = nat-map α i (nat-map β i x) 
nat-com (sem-subcomp {κ} Γ₁ Γ₂ Γ₃ α β) i j x =
  begin
    Mor Γ₃ i j (nat-map α i (nat-map β i x))
  ≡⟨ nat-com α i j (nat-map β i x) ⟩
    nat-map α j (Mor Γ₂ i j (nat-map β i x))
  ≡⟨ cong (nat-map α j) (nat-com β i j x) ⟩
    nat-map α j (nat-map β j (Mor Γ₁ i j x))
  ∎
\end{code}

\begin{code}
sem-subst-tm : {Δ : ClockCtx} (Γ₁ Γ₂ : SemCtx Δ) (A : SemTy Δ) → SemSub Γ₁ Γ₂ → SemTm Γ₁ A → SemSub Γ₁ (Γ₂ ,, A)
sem-subst-tm {∅} Γ₁ Γ₂ A α t x = α x , t x
nat-map (sem-subst-tm {κ} Γ₁ Γ₂ A α t) i x = nat-map α i x , nat-map t i x
nat-com (sem-subst-tm {κ} Γ₁ Γ₂ A α t) i j x =
  begin
    (Mor Γ₂ i j (nat-map α i x) , Mor A i j (nat-map t i x))
  ≡⟨ cong (λ z → (_ , z)) (nat-com t i j x) ⟩
    (Mor Γ₂ i j (nat-map α i x) , nat-map t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (z , _)) (nat-com α i j x) ⟩
    (nat-map α j (Mor Γ₁ i j x) , nat-map t j (Mor Γ₁ i j x))
  ∎
\end{code}

\begin{code}
sem-subpr : {Δ : ClockCtx} (Γ₁ Γ₂ : SemCtx Δ) (A : SemTy Δ) → SemSub Γ₁ (Γ₂ ,, A) → SemSub Γ₁ Γ₂
sem-subpr {∅} Γ₁ Γ₂ A α z = proj₁ (α z)
nat-map (sem-subpr {κ} Γ₁ Γ₂ A α) i x = proj₁ (nat-map α i x)
nat-com (sem-subpr {κ} Γ₁ Γ₂ A α) i j x = cong proj₁ (nat-com α i j x)
\end{code}
}
