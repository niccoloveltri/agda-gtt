\AgdaHide{
\begin{code}
module Prelude.Interpretation where

open import Prelude.Syntax
\end{code}
}

We now define the notion of interpretation of \GTT.
To interpret types, one must give a type of semantical types and a function mapping each syntactic type to its semantical counterpart.
Similarly for contexts, terms, substitutions and definitional equalities.
This leads to the following record where we only show the fields related to types.

\begin{code}
record interpret-syntax : Set₂ where
  field
    semTy : ClockCtx → Set₁
    _⟦_⟧Ty : ∀ {Δ} → Ty Δ → semTy Δ
\end{code}

\AgdaHide{
\begin{code}
    semCtx : ClockCtx → Set₁
    semTm : ∀ {Δ} → semCtx Δ → semTy Δ → Set
    semSub : ∀ {Δ} → semCtx Δ → semCtx Δ → Set
    _[_sem∼_] : ∀ {Δ} {Γ : semCtx Δ} {A : semTy Δ}
      → semTm Γ A → semTm Γ A → Set
    _[_sem≈_] : ∀ {Δ} {Γ₁ Γ₂ : semCtx Δ} → semSub Γ₁ Γ₂ → semSub Γ₁ Γ₂ → Set
    _⟦_⟧Ctx : ∀ {Δ} → Ctx Δ → semCtx Δ
    _⟦_⟧Tm : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → semTm (_⟦_⟧Ctx Γ) (_⟦_⟧Ty A)
    _⟦_⟧Sub : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → semSub (_⟦_⟧Ctx Γ₁) (_⟦_⟧Ctx Γ₂)
    _⟦_⟧∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t t' : Tm Γ A}
      → t ∼ t' → _[_sem∼_] (_⟦_⟧Tm t) (_⟦_⟧Tm t')
    _⟦_⟧≈ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {s s' : Sub Γ₁ Γ₂}
      → s ≈ s' → _[_sem≈_] (_⟦_⟧Sub s) (_⟦_⟧Sub s')
\end{code}
}
