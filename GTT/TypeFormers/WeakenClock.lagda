\AgdaHide{
\begin{code}
module GTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import Presheaves.Const
open import GTT.Structure

open NatTrans
\end{code}
}

Similarly to the weakening type former \IC{⇡}, the weakening context former \IC{⇡} is modeled using the constant presheaf \F{Const}.
%% is a map which takes a context in the empty clock
%% context and maps it to one in the clock context with just one clock.
%% Concretely, we define a presheaf using a type, and we do this via the constant presheaf.
\begin{code}
⇑ : SemCtx ∅ → SemCtx κ
⇑ Γ = Const Γ
\end{code}
\AgdaHide{
\begin{code}
sem-up : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm Γ A → SemTm (⇑ Γ) (⇑ A)
nat-map (sem-up Γ A t) _ = t
nat-com (sem-up Γ A t) _ _ _ = refl
\end{code}

\begin{code}
sem-down : (Γ : SemCtx ∅) (A : SemTy ∅) → SemTm (⇑ Γ) (⇑ A) → SemTm Γ A 
sem-down Γ A t = nat-map t ∞
\end{code}
}
