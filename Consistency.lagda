\AgdaHide{
\begin{code}
module Consistency where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Level
open import Prelude
open import Prelude.Syntax
open import Prelude.Interpretation
open import Presheaves
open import GTT

open interpret-syntax
\end{code}
}

%If \AB{sem} is an interpretation of the syntax and \AB{t} is a term, then we write \AB{sem} \AFi{⟦} \AB{t} \AFi{⟧} for the interpretation of \AB{t}.
\remove{
The primary example is the syntax itself.
Types, contexts, substitutions, terms, and so on are interpreted by themselves.
This gives rise to the initial interpretation.
}

\remove{
We also define categorical semantics of the syntax by using the material in \Cref{sec:presheaf_sem,sec:guarded}.
Types and contexts are interpreted as presheaves, and terms are interpreted as natural transformations.
Formally, we define an interpretation \F{sem}.
}
\begin{code}
sem : interpret-syntax
semTy sem = SemTy
_⟦_⟧Ty sem = ⟦_⟧type
\end{code}

\AgdaHide{
\begin{code}
semCtx sem = SemCtx
semTm sem = SemTm
semSub sem = SemSub
_[_sem∼_] sem = def-eq _ _
_[_sem≈_] sem = subst-eq _ _
_⟦_⟧Ctx sem = ⟦_⟧Γ
_⟦_⟧Sub sem = ⟦_⟧sub
_⟦_⟧Tm sem = ⟦_⟧tm
_⟦_⟧∼ sem = ⟦_⟧tm-eq
_⟦_⟧≈ sem = ⟦_⟧sub-eq
\end{code}
}

Using the interpetation \F{sem}, we can show that \GTT\ is consistent, by which we mean that
not every definitional equality is deducible. 
%that not every definitional equality holds.
We first define a type \F{bool} : \F{Ty} \IC{∅} as \IC{𝟙 ⊞ 𝟙} and two terms \F{TRUE} and \F{FALSE} as \IC{in₁ tt} and \IC{in₂ tt} respectively, where \IC{in₁} and \IC{in₂} are the two constructors of \IC{⊞}.
We say that \GTT\ is consistent if \AF{TRUE} and \AF{FALSE} are not definitionally equal.
\AgdaHide{
\begin{code}
bool : Ty ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Tm • bool
TRUE = in₁ 𝟙 tt

FALSE : Tm • bool
FALSE = in₂ 𝟙 tt
\end{code}
}
\begin{code}
consistent : Set
consistent = TRUE ∼ FALSE → ⊥
\end{code}

This is proved by noticing that if \F{TRUE} were definitionally equal to \F{FALSE}, then their interpretations in \AD{sem} would be equal.
However, they are interpreted as \AIC{inj₁} \AIC{tt} and \AIC{inj₂} \AIC{tt} respectively, and those are unequal.
Hence, \GTT is consistent.
\AgdaHide{
\begin{code}
--consistent : ∀ {ℓ₁ ℓ₂} → interpret-syntax {ℓ₁} {ℓ₂} → Set ℓ₂
--consistent sem = sem [ sem ⟦ TRUE ⟧Tm sem∼ sem ⟦ FALSE ⟧Tm ] → ⊥
sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥
\end{code}

\begin{code}
--sem-consistent : consistent sem
\end{code}

\begin{code}
--sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}
}
\remove{
Note that the categorical semantics gives rises to a consistent interpretation of the syntax, because \AIC{inj₁} \AIC{tt} and \AIC{inj₂} \AIC{tt} are unequal where \AIC{tt} is the constructor of \AD{⊤}.
From this, we conclude that the initial interpretation is consistent.
This is because whenever we have a definitional equality between \AF{TRUE} and \AF{FALSE}, we could interpret that equality in \AF{sem}.
Since the latter leads to a contradiction, the former does so too.
All in all, we get
}
\AgdaHide{
\begin{code}
syntax-consistent : consistent
syntax-consistent p with (sem ⟦ p ⟧∼) tt
syntax-consistent p | ()
\end{code}

\begin{code}
sub-π₁ : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⊠ B)) (s : Sub Γ₂ Γ₁)
  → sub (π₁ t) s ∼ π₁ (sub t s)
sub-π₁ t s =
  trans∼ (sym∼ (⊠-β₁ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₁ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-π₂ : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⊠ B)) (s : Sub Γ₂ Γ₁)
  → sub (π₂ t) s ∼ π₂ (sub t s)
sub-π₂ t s =
  trans∼ (sym∼ (⊠-β₂ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₂ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-app : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⟶ B)) (s : Sub Γ₂ Γ₁)
  → sub (app t) (upA A s) ∼ app (sub t s)
sub-app t s =
  trans∼ (sym∼ (λ-β _))
         (trans∼ (cong-app (sym∼ (sub-lambda (app t) s)))
                 (cong-app (cong-sub (λ-η t) refl≈)))

sub-unbox : {Γ₁ Γ₂ : Ctx ∅} {A : Ty κ} (t : Tm Γ₁ (□ A)) (s : Sub Γ₂ Γ₁)
  → sub (unbox t) (up s) ∼ unbox (sub t s)
sub-unbox t s =
  trans∼ (sym∼ (□-β (sub (unbox t) (up s))))
         (cong-unbox (trans∼ (sym∼ (sub-box (unbox t) s)) (cong-sub (□-η t) refl≈)))

sub-down : {Γ₁ Γ₂ : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ₁) (⇡ A)) (s : Sub Γ₂ Γ₁)
  → sub (down t) s ∼ down(sub t (up s))
sub-down t s =
  trans∼ (sym∼ (up-β (sub (down t) s)))
         (cong-down (trans∼ (sym∼ (sub-up (down t) s)) (cong-sub (up-η t) refl≈)))

sub-tt : {Γ₁ Γ₂ : Ctx ∅} (s : Sub Γ₂ Γ₁) → sub tt s ∼ tt
sub-tt s = 𝟙-η (sub tt s)
\end{code}
}
