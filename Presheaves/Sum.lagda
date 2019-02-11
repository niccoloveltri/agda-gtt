\AgdaHide{
\begin{code}
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

open PSh

module _ (P Q : PSh) where
\end{code}

  \begin{code}
  SumObj : Size → Set
  SumObj i = Obj P i ⊎ Obj Q i
  \end{code}

  \begin{code}
  SumMor : (i : Size) (j : Size< (↑ i))
    → SumObj i → SumObj j
  SumMor i j = map (Mor P i j) (Mor Q i j)
  \end{code}
  
  \begin{code}
  SumMorId : {i : Size} {x : SumObj i}
    → SumMor i i x ≡ x
  SumMorId {i} {inj₁ p} =
    begin
      inj₁ (Mor P i i p)
    ≡⟨ cong inj₁ (MorId P) ⟩
      inj₁ p
    ∎
  SumMorId {i} {inj₂ q} =
    begin
      inj₂ (Mor Q i i q)
    ≡⟨ cong inj₂ (MorId Q) ⟩
      inj₂ q
    ∎
  \end{code}

  \begin{code}
  SumMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : SumObj i}
    → SumMor i k x ≡ SumMor j k (SumMor i j x)
  SumMorComp {i} {j} {k} {inj₁ p} =
    begin
      inj₁ (Mor P i k p)
    ≡⟨ cong inj₁ (MorComp P) ⟩
      inj₁ (Mor P j k (Mor P i j p))
    ∎
  SumMorComp {i} {j} {k} {inj₂ q} =
    begin
      inj₂ (Mor Q i k q)
    ≡⟨ cong inj₂ (MorComp Q) ⟩
      inj₂ (Mor Q j k (Mor Q i j q))
    ∎
  \end{code}
}

In addition, there are several constructions to make presheaves from other presheaves.
The first two are defined pointwise.
We can take the sum of presheaves by taking the sum on each coordinate.
For the morphisms, we use functoriality of taking sums.

\begin{code}
Sum : PSh → PSh → PSh
\end{code}

\AgdaHide{
\begin{code}
Sum P Q = record
  { Obj = SumObj P Q
  ; Mor = SumMor P Q
  ; MorId = SumMorId P Q
  ; MorComp = λ {_}{_}{_}{x} → SumMorComp P Q {x = x}
  }
\end{code}
}
