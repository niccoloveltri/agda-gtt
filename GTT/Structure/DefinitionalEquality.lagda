\AgdaHide{
\begin{code}
module GTT.Structure.DefinitionalEquality where

open import Data.Product
open import Prelude
open import Presheaves
open import GTT.Structure.Contexts
open import GTT.Structure.Types
open import GTT.Structure.Terms
open import GTT.Structure.Subst

open PSh
open NatTrans
\end{code}
}

Equality of semantic terms and substitutions is defined as propositional equality.
%Since we assume both function extensionality and UIP, we can formulate this in a more convenient way.

\AgdaHide{
\begin{code}
def-eq : ∀ {Δ} (Γ : SemCtx Δ) (A : SemTy Δ) (s t : SemTm Γ A) → Set
def-eq {∅} Γ A s t = (x : Γ) → s x ≡ t x
def-eq {κ} Γ A s t = (i : Size) (x : Obj Γ i) → nat-map s i x ≡ nat-map t i x
\end{code}

\begin{code}
refl-def-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {t : SemTm Γ A}
  → def-eq Γ A t t
refl-def-eq {∅} γ = refl
refl-def-eq {κ} i γ = refl

sym-def-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t : SemTm Γ A}
  → def-eq Γ A s t → def-eq Γ A t s
sym-def-eq {∅} p γ = sym (p γ)
sym-def-eq {κ} p i γ = sym (p i γ)

trans-def-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t u : SemTm Γ A}
  → def-eq Γ A s t → def-eq Γ A t u → def-eq Γ A s u
trans-def-eq {∅} p q γ = trans (p γ) (q γ)
trans-def-eq {κ} p q i γ = trans (p i γ) (q i γ)

eq-to-def-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t : SemTm Γ A}
  → s ≡ t → def-eq Γ A s t
eq-to-def-eq refl = refl-def-eq

def-eq-to-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t : SemTm Γ A}
  → def-eq Γ A s t → s ≡ t
def-eq-to-eq {∅} p = funext p
def-eq-to-eq {κ} p = NatTrans-eq p

eq-to-def-eq-to-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t : SemTm Γ A}
  → (p : def-eq Γ A s t) → eq-to-def-eq(def-eq-to-eq p) ≡ p
eq-to-def-eq-to-eq {∅} p = funext (λ _ → uip)
eq-to-def-eq-to-eq {κ} p = funext (λ _ → funext (λ _ → uip))

def-eq-to-eq-to-def-eq : ∀ {Δ} {Γ : SemCtx Δ} {A : SemTy Δ} {s t : SemTm Γ A}
  → (p : s ≡ t) → def-eq-to-eq(eq-to-def-eq p) ≡ p
def-eq-to-eq-to-def-eq p = uip
\end{code}

\begin{code}
subst-eq : ∀ {Δ} (Γ Γ' : SemCtx Δ) (s t : SemSub Γ Γ') → Set
subst-eq {∅} Γ Γ' s t = (x : Γ) → s x ≡ t x
subst-eq {κ} Γ Γ' s t = (i : Size) (x : Obj Γ i) → nat-map s i x ≡ nat-map t i x
\end{code}

\begin{code}
refl-subst-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s : SemSub Γ Γ'}
  → subst-eq Γ Γ' s s
refl-subst-eq {∅} x = refl
refl-subst-eq {κ} i x = refl

sym-subst-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t : SemSub Γ Γ'}
  → subst-eq Γ Γ' s t → subst-eq Γ Γ' t s
sym-subst-eq {∅} p γ = sym (p γ)
sym-subst-eq {κ} p i γ = sym (p i γ)

trans-subst-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t u : SemSub Γ Γ'}
  → subst-eq Γ Γ' s t → subst-eq Γ Γ' t u → subst-eq Γ Γ' s u
trans-subst-eq {∅} p q γ = trans (p γ) (q γ)
trans-subst-eq {κ} p q i γ = trans (p i γ) (q i γ)

eq-to-subst-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t : SemSub Γ Γ'}
  → s ≡ t → subst-eq Γ Γ' s t
eq-to-subst-eq refl = refl-subst-eq

subst-eq-to-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t : SemSub Γ Γ'}
  → subst-eq Γ Γ' s t → s ≡ t
subst-eq-to-eq {∅} p = funext p
subst-eq-to-eq {κ} p = NatTrans-eq p

subst-eq-to-eq-to-subst-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t : SemSub Γ Γ'}
  → (p : s ≡ t)
  → subst-eq-to-eq(eq-to-subst-eq p) ≡ p
subst-eq-to-eq-to-subst-eq p = uip

eq-to-subst-eq-to-eq : ∀ {Δ} {Γ Γ' : SemCtx Δ} {s t : SemSub Γ Γ'}
  → (p : subst-eq Γ Γ' s t)
  → eq-to-subst-eq(subst-eq-to-eq p) ≡ p
eq-to-subst-eq-to-eq {∅} p = funext (λ _ → uip)
eq-to-subst-eq-to-eq {κ} p = funext (λ _ → funext (λ _ → uip))
\end{code}
}
