\AgdaHide{
\begin{code}
module GTT.Structure.ContextOperations where

open import Data.Unit
open import Data.Product
open import Prelude
open import Presheaves
open import GTT.Structure.Contexts
open import GTT.Structure.Types
open import GTT.Structure.Terms

open NatTrans
\end{code}
}

\AgdaHide{
\begin{code}
∙ : (b : ClockCtx) → SemCtx b
∙ ∅ = ⊤
∙ κ = Terminal
\end{code}

\begin{code}
_,,_ : {b : ClockCtx} → SemCtx b → SemTy b → SemCtx b
_,,_ {∅} Γ A = Γ × A
_,,_ {κ} Γ A = Prod Γ A
\end{code}

\begin{code}
sem-var : {b : ClockCtx} (Γ : SemCtx b) (A : SemTy b) → SemTm (Γ ,, A) A
sem-var {∅} Γ A = proj₂
nat-map (sem-var {κ} Γ A) i (γ , x) = x
nat-com (sem-var {κ} Γ A) i j (γ , x) = refl
\end{code}

\begin{code}
weaken : {b : ClockCtx} (Γ : SemCtx b) (A B : SemTy b) → SemTm Γ B → SemTm (Γ ,, A) B
weaken {∅} Γ A B t (x , _) = t x
nat-map (weaken {κ} Γ A B t) i (x₁ , x₂) = nat-map t i x₁
nat-com (weaken {κ} Γ A B t) i j (x₁ , x₂) = nat-com t i j x₁
\end{code}
}
