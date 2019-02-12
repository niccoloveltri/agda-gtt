
module GTT.Structure.Terms where

open import Data.Product
open import Prelude
open import GTT.Structure.Contexts
open import GTT.Structure.Types

open PSh

-- Semantic terms
SemTm : {Δ : ClockCtx} (Γ : SemCtx Δ) (A : SemTy Δ) → Set
SemTm {∅} Γ A = Γ → A
SemTm {κ} Γ A = NatTrans Γ A

