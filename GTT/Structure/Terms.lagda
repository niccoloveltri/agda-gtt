\AgdaHide{
\begin{code}
module GTT.Structure.Terms where

open import Data.Product
open import Prelude
open import GTT.Structure.Contexts
open import GTT.Structure.Types

open PSh
\end{code}
}

The semantic terms of type $A$ in context $\Gamma$ are functions from $\Gamma$ to $A$ if the clock context is empty, and they are natural transformations between $\Gamma$ and $A$ otherwise.
%% Again we need to distinguish two cases, because morphisms between sets are something different than morphisms between presheaves.
%% For sets, we just use functions. 
%% For presheaves, we use natural transformations instead.
\begin{code}
SemTm : {Δ : ClockCtx} (Γ : SemCtx Δ) (A : SemTy Δ) → Set
SemTm {∅} Γ A = Γ → A
SemTm {κ} Γ A = NatTrans Γ A
\end{code}
