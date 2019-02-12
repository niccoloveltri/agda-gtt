
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
open import GTT.Structure
open import Prelude.Interpretation
open import GTT.InterpretSyntax
open import GTT.DefinitionalEqualities

open interpret-syntax

-- Soundness of the interpretation
sem : interpret-syntax
semTy sem = SemTy
_⟦_⟧Ty sem = ⟦_⟧type
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


-- Consistency of GTT
bool : Ty ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Tm • bool
TRUE = in₁ 𝟙 tt

FALSE : Tm • bool
FALSE = in₂ 𝟙 tt

consistent : Set
consistent = TRUE ∼ FALSE → ⊥

sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥

syntax-consistent : consistent
syntax-consistent p with (sem ⟦ p ⟧∼) tt
syntax-consistent p | ()


