\AgdaHide{
\begin{code}
module Presheaves.NaturalTransformations where

open import Prelude
open import Presheaves.Presheaves
open PSh
\end{code}
}

Beside presheaves, we also need natural transformations.
These are defined as a record \F{NatTrans}, consisting of a map \Fi{nat-map} and a proof of the usual commutativity requirement.
%More precisely, we use the following record
\begin{code}
record NatTrans (P Q : PSh) : Set where
  field
    nat-map : (i : Size) → Obj P i → Obj Q i
    nat-com : (i : Size) (j : Size< (↑ i)) (x : Obj P i)
      → Mor Q i j (nat-map i x) ≡ nat-map j (Mor P i j x)
\end{code}

\AgdaHide{
\begin{code}
open NatTrans

NatTrans-eq' : {P Q : PSh} {s t : NatTrans P Q} → nat-map s ≡ nat-map t → s ≡ t
NatTrans-eq' {_} {_} {s} {t} refl =
  cong (λ z → record {nat-map = nat-map t ; nat-com = z})
       (funext (λ _ → funext (λ {_ → funext (λ _ → uip)})))

NatTrans-eq : {P Q : PSh} {s t : NatTrans P Q} → ((i : Size) (x : Obj P i) → nat-map s i x ≡ nat-map t i x) → s ≡ t
NatTrans-eq p = NatTrans-eq' (funext (λ i → funext (λ x → p i x)))
\end{code}
}
