
module GTT.Structure.Contexts where

open import Prelude
open import Presheaves public

-- Semantic contexts
SemCtx : ClockCtx → Set₁
SemCtx ∅ = Set
SemCtx κ = PSh
