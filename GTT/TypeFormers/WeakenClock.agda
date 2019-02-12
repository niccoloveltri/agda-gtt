
module GTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import Presheaves.Const
open import GTT.Structure

open NatTrans

-- Semantic context (and type) weakening
⇑ : SemCtx ∅ → SemCtx κ
⇑ Γ = Const Γ

-- Interpretation of the term (and substitution) constructors "up" and "down"
sem-up : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm Γ A → SemTm (⇑ Γ) (⇑ A)
nat-map (sem-up Γ A t) _ = t
nat-com (sem-up Γ A t) _ _ _ = refl

sem-down : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm (⇑ Γ) (⇑ A) → SemTm Γ A 
sem-down Γ A t = nat-map t ∞

