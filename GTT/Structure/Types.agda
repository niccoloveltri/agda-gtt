
module GTT.Structure.Types where

open import Prelude
open import Presheaves public

-- Semantic types
SemTy : ClockCtx → Set₁
SemTy ∅ = Set
SemTy κ = PSh

