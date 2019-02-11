\AgdaHide{
\begin{code}
module Presheaves.Exp where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open PSh
\end{code}
}
Function spaces are defined as the exponential of presheaves.
%Here we only present how to define the action on the objects of this presheaf.
The action on a size \Ar{i} of this presheaf consists of natural transformations restricted to sizes smaller or equal than \Ar{i}.
\begin{code}
record ExpObj (P Q : PSh) (i : Size) : Set where
  field
    fun : (j : Size< (↑ i)) → Obj P j → Obj Q j
    funcom : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj P j)
      → Mor Q j k (fun j x) ≡ fun k (Mor P j k x)
\end{code}

\AgdaHide{
\begin{code}
open ExpObj

funeq' : {P Q : PSh} {i : Size} {s t : ExpObj P Q i} → fun s ≡ fun t → s ≡ t
funeq' {P} {Q} {_} {s} {t} refl = cong (λ z → record { fun = fun t ; funcom = z }) (funext (λ _ → funext (λ _ → funext (λ _ → uip))))

funeq : {P Q : PSh} {i : Size} {s t : ExpObj P Q i} → ((j : Size< (↑ i)) (x : Obj P j) → fun s j x ≡ fun t j x) → s ≡ t
funeq p = funeq' (funext (λ j → funext (λ x → p j x)))
\end{code}

\begin{code}
module _ (P Q : PSh) where
\end{code}
  \begin{code}
  ExpMor : (i : Size) (j : Size< (↑ i))
    → ExpObj P Q i → ExpObj P Q j
  ExpMor i j f = f
  \end{code}

  \begin{code}
  ExpMorId : {i : Size} {x : ExpObj P Q i}
    → ExpMor i i x ≡ x
  ExpMorId = refl
  \end{code}
  
  \begin{code}
  ExpMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ExpObj P Q i}
    → ExpMor i k x ≡ ExpMor j k (ExpMor i j x)
  ExpMorComp = refl
  \end{code}

\begin{code}
Exp : PSh → PSh → PSh
\end{code}

\begin{code}
Exp P Q = record
  { Obj = ExpObj P Q
  ; Mor = ExpMor P Q
  ; MorId = ExpMorId P Q
  ; MorComp = ExpMorComp P Q
  }
\end{code}
}
