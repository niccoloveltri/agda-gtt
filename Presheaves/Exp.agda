
module Presheaves.Exp where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open PSh


-- Exponentials of presheaves
module _ (P Q : PSh) where

  record ExpObj (i : Size) : Set where
    field
      fun : (j : Size< (↑ i)) → Obj P j → Obj Q j
      funcom : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj P j)
        → Mor Q j k (fun j x) ≡ fun k (Mor P j k x)

  ExpMor : (i : Size) (j : Size< (↑ i))
    → ExpObj i → ExpObj j
  ExpMor i j f = f

  ExpMorId : {i : Size} {x : ExpObj i}
    → ExpMor i i x ≡ x
  ExpMorId = refl

  ExpMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ExpObj i}
    → ExpMor i k x ≡ ExpMor j k (ExpMor i j x)
  ExpMorComp = refl

open ExpObj

Exp : PSh → PSh → PSh
Exp P Q = record
  { Obj = ExpObj P Q
  ; Mor = ExpMor P Q
  ; MorId = ExpMorId P Q
  ; MorComp = ExpMorComp P Q
  }

-- -- A characterization of equality of terms in ExpObj P Q i
funeq' : {P Q : PSh} {i : Size} {s t : ExpObj P Q i} → fun s ≡ fun t → s ≡ t
funeq' {P} {Q} {_} {s} {t} refl = cong (λ z → record { fun = fun t ; funcom = z }) (funext (λ _ → funext (λ _ → funext (λ _ → uip))))

funeq : {P Q : PSh} {i : Size} {s t : ExpObj P Q i} → ((j : Size< (↑ i)) (x : Obj P j) → fun s j x ≡ fun t j x) → s ≡ t
funeq p = funeq' (funext (λ j → funext (λ x → p j x)))
