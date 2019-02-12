
module GTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure
open import GTT.TypeFormers.Later
open import GTT.TypeFormers.Box

open PSh
open ■
open ►Obj

-- Interpretation of force
sem-force' : (A : SemTy κ) → ■ (► A) → ■ A
■cone (sem-force' A t) i = ►cone (■cone t ∞) [ i ]
■com (sem-force' A t) i j = ►com (■cone t ∞) [ i ] [ j ]

sem-force : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ (► A))) → SemTm Γ (■ A)
sem-force Γ A t x = sem-force' A (t x)

