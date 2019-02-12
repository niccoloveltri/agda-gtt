
module GTT.TypeFormers.Later where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure

open PSh

-- An inductive analogue of the predicate Size<,
-- used for defining a terminating semantic fixpoint combinator
data SizeLt (i : Size) : Set where
  [_] : Size< i → SizeLt i

-- SizeLt embeds into Size
size : ∀ {i} → SizeLt i → Size
size [ j ] = j

-- Functions with domain SizeLt i can be specified
-- using functions on Size< i
elimLt : {A : Size → Set₁} {i : Size} → ((j : Size< i) → A j)
  → (j : SizeLt i) → A (size j)
elimLt f [ j ] = f j

-- Two auxiliary definitions, used in the construction
-- of the action on objects of the semantic later modality
Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)

LaterLim : (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)
  → (i : Size) (x : Later A i) → Set
LaterLim A m i x = (j : SizeLt i)
  → elimLt (λ { j' → (k : SizeLt (↑ j'))
    → elimLt (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) k }) j

-- An auxiliary definition, used in the construction of
-- the action on morphism of the semantic later modality
module _ (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)  where

  LaterLimMor : (i : Size) (j : Size< (↑ i)) (x : Later A i)
    → LaterLim A m i x → LaterLim A m j x
  LaterLimMor i j x p [ k ] [ l ] = p [ k ] [ l ]

-- Action on objects of the semantic later modality
record ►Obj (A : SemTy κ) (i : Size) : Set where
  field
    ►cone : Later (Obj A) i
    ►com : LaterLim (Obj A) (Mor A) i ►cone
open ►Obj

-- A characterization of equality of terms in ►Obj A i
►eq' : {A : SemTy κ} {i : Size} {s t : ►Obj A i} → ►cone s ≡ ►cone t → s ≡ t
►eq' {_} {s} {t} refl = cong (λ z → record { ►cone = ►cone t ; ►com = z})
                             (funext (λ {[ j ] → funext (λ {[ k ] → uip})}))

►eq : {A : SemTy κ} {i : Size} {s t : ►Obj A i} → ((j : Size< i) → ►cone s [ j ] ≡ ►cone t [ j ]) → s ≡ t
►eq p = ►eq' (funext (λ {[ j ] → p j}))

-- Rest of the data of the semantic later modality
module _ (A : SemTy κ) where

  ►Mor : (i : Size) (j : Size< (↑ i))
    → ►Obj A i → ►Obj A j
  ►cone (►Mor i j t) = ►cone t
  ►com (►Mor i j t) = LaterLimMor (Obj A) (Mor A) i j (►cone t) (►com t)
  
  ►MorId : {i : Size} {x : ►Obj A i}
    → ►Mor i i x ≡ x
  ►MorId = ►eq (λ {j → refl})
  
  ►MorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : ►Obj A i}
               → ►Mor i k x ≡ ►Mor j k (►Mor i j x)
  ►MorComp = ►eq (λ {j → refl})

► : SemTy κ → SemTy κ
► A = record
    { Obj = ►Obj A
    ; Mor = ►Mor A
    ; MorId = ►MorId A
    ; MorComp = ►MorComp A
    }

