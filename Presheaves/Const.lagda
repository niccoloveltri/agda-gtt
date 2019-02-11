\AgdaHide{
\begin{code}
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

module _ (A : Set) where
\end{code}


  \begin{code}
  ConstObj : Size → Set
  ConstObj i = A
  \end{code}

  \begin{code}
  ConstMor : (i : Size) (j : Size< (↑ i))
    → ConstObj i → ConstObj j
  ConstMor i j x = x
  \end{code}

  \begin{code}
  ConstMorId : {i : Size} {x : A}
    → ConstMor i i x ≡ x
  ConstMorId = refl
  \end{code}
  
  \begin{code}
  ConstMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ConstObj i}
    → ConstMor i k x ≡ ConstMor j k (ConstMor i j x)
  ConstMorComp = refl
  \end{code}
}

Products and sums of presheaves are defined pointwise.
The weakening type former \IC{↑} of \GTT\ is modeled using the constant presheaf, which we denote by \AF{Const}.
\AgdaHide{
\begin{code}
Const : Set → PSh
\end{code}

\begin{code}
Const A = record
  { Obj = ConstObj A
  ; Mor = ConstMor A
  ; MorId = ConstMorId A
  ; MorComp = ConstMorComp A
  }
\end{code}
}
