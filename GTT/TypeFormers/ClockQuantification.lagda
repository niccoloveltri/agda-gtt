\AgdaHide{
\begin{code}
module GTT.TypeFormers.ClockQuantification where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure
open import GTT.TypeFormers.WeakenClock
open import GTT.TypeFormers.FunctionType

open PSh
open NatTrans
\end{code}
}

M{\o}gelberg models universal clock
quantification by taking limits \cite{Mogelberg14}. We define the semantic box modality \F{■} similarly:
given a presheaf \Ar{A},
we take \F{■} \Ar{A} to be the limit of \Ar{A}. Formally, the limit of
\Ar{A} is constructed as a record with two fields. The field \AFi{■cone}
is given by a family \Ar{f i} in \Fi{Obj} \Ar{A i} for each size
\Ar{i}.  The field \AFi{■com} is a proof that the restriction of \Ar{f
i} to a size \Ar{j} smaller than \Ar{i} is equal to \Ar{f j}.
\begin{code}
record ■ (A : SemTy κ) : SemTy ∅ where
  field
    ■cone : (i : Size) → Obj A i
    ■com : (i : Size) (j : Size< (↑ i)) → Mor A i j (■cone i) ≡ ■cone j
\end{code}
\AgdaHide{
\begin{code}
open ■

■eq' : {A : SemTy κ} {s t : ■ A} → ■cone s ≡ ■cone t → s ≡ t
■eq' {_} {s} {t} refl = cong (λ z → record { ■cone = ■cone s ; ■com = z })
                             (funext (λ _ → funext λ _ → uip))

■eq : {A : SemTy κ} {s t : ■ A} → ((i : Size) → ■cone s i ≡ ■cone t i) → s ≡ t
■eq p = ■eq' (funext p)
\end{code}
}

The semantic box modality is right adjoint to context
weakening. In other words, the types \F{Tm} (\F{⇑} \Ar{Γ})
\Ar{A} and \F{Tm} \Ar{Γ} (\F{■} \Ar{A}) are isomorphic for all \Ar{Γ} and \Ar{A}. The function
underlying the isomorphism is \F{sem-box} and its inverse is \F{sem-unbox}, modeling \IC{box} and \IC{unbox} respectively.
\begin{code}
sem-box : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm (⇑ Γ) A) → SemTm Γ (■ A)
■cone (sem-box Γ A t x) i        = nat-map t i x
■com (sem-box Γ A t x) i j       = nat-com t i j x

sem-unbox : (Γ : SemCtx ∅) (A : SemTy κ) (t : SemTm Γ (■ A)) → SemTm (⇑ Γ) A
nat-map (sem-unbox Γ A t) i x    = ■cone (t x) i
nat-com (sem-unbox Γ A t) i j x  = ■com (t x) i j
\end{code}
