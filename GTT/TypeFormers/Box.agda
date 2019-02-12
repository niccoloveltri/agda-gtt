
module GTT.TypeFormers.Box where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure
open import GTT.TypeFormers.WeakenClock
open import GTT.TypeFormers.FunctionType

open PSh
open NatTrans

-- Semantic box modality
record ■ (A : SemTy κ) : SemTy ∅ where
  field
    ■cone : (i : Size) → Obj A i
    ■com : (i : Size) (j : Size< (↑ i)) → Mor A i j (■cone i) ≡ ■cone j
open ■

-- A characterization of equality for ■
■eq' : {A : SemTy κ} {s t : ■ A} → ■cone s ≡ ■cone t → s ≡ t
■eq' {_} {s} {t} refl = cong (λ z → record { ■cone = ■cone s ; ■com = z })
                             (funext (λ _ → funext λ _ → uip))

■eq : {A : SemTy κ} {s t : ■ A} → ((i : Size) → ■cone s i ≡ ■cone t i) → s ≡ t
■eq p = ■eq' (funext p)

-- Interpretation of the term constructors "box" and "unbox"
sem-box : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm (⇑ Γ) A) → SemTm Γ (■ A)
■cone (sem-box Γ A t x) i        = nat-map t i x
■com (sem-box Γ A t x) i j       = nat-com t i j x

sem-unbox : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ A)) → SemTm (⇑ Γ) A
nat-map (sem-unbox Γ A t) i x    = ■cone (t x) i
nat-com (sem-unbox Γ A t) i j x  = ■com (t x) i j

