
module GTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import GTT.Structure
open import GTT.TypeFormers.Later
open import GTT.TypeFormers.SumType
open import GTT.TypeFormers.ProductType
open import GTT.TypeFormers.FunctionType
open import GTT.TypeFormers.WeakenClock

open PSh

-- Semantic codes for functors
data SemCode : ClockCtx → Set₁ where
    ∁ : ∀ {Δ} → SemTy Δ → SemCode Δ
    I : ∀ {Δ} → SemCode Δ
    _⊞_ _⊠_ : ∀ {Δ} → SemCode Δ → SemCode Δ → SemCode Δ
    ▸ : SemCode κ → SemCode κ

-- Evaluation of codes as functors on SemTy Δ.
sem-eval : ∀ {Δ} → SemCode Δ → SemTy Δ → SemTy Δ
sem-eval (∁ A) X = A
sem-eval I X = X
sem-eval (P ⊞ Q) X = sem-eval P X ⊕ sem-eval Q X
sem-eval (P ⊠ Q) X = sem-eval P X ⊗ sem-eval Q X
sem-eval (▸ P) X = ►(sem-eval P X)

-- Semantic μ-types in the ∅ clock context
data μset (P : SemCode ∅) : SemCode ∅ → Set where
  ∁s : {X : Set} → X → μset P (∁ X)
  I : μset P P → μset P I
  _⊠_ : {Q R : SemCode ∅} → μset P Q → μset P R → μset P (Q ⊠ R)
  ⊞₁ : {Q R : SemCode ∅} → μset P Q → μset P (Q ⊞ R)
  ⊞₂ : {Q R : SemCode ∅} → μset P R → μset P (Q ⊞ R)

-- Action on objects and on morphisms of the semantic μ-types.
-- They are defined simultaneoulsy, because LaterLim depends on
-- a sized type and a proof that it is antitone.
mutual
  data muObj' (P : SemCode κ) : SemCode κ → Size → Set where
    const : {X : PSh} {i : Size} → Obj X i → muObj' P (∁ X) i
    rec : ∀{i} → muObj' P P i → muObj' P I i
    _,_ : ∀{Q R i} → muObj' P Q i → muObj' P R i → muObj' P (Q ⊠ R) i
    in₁ : ∀{Q R i} → muObj' P Q i → muObj' P (Q ⊞ R) i
    in₂ : ∀{Q R i} → muObj' P R i → muObj' P (Q ⊞ R) i
    later : ∀{Q i} (x : Later (muObj' P Q) i)
      → LaterLim (muObj' P Q) (muMor' P Q) i x → muObj' P (▸ Q) i

  muMor' : (P Q : SemCode κ) (i : Size) (j : Size< (↑ i)) → muObj' P Q i → muObj' P Q j
  muMor' P (∁ X) i j (const x) = const (Mor X i j x)
  muMor' P I i j (rec x) = rec (muMor' P P i j x)
  muMor' P (Q ⊠ R) i j (x , y) = muMor' P Q i j x , muMor' P R i j y
  muMor' P (Q ⊞ R) i j (in₁ x) = in₁ (muMor' P Q i j x)
  muMor' P (Q ⊞ R) i j (in₂ x) = in₂ (muMor' P R i j x)
  muMor' P (▸ Q) i j (later x p) = later x (λ { [ k ] → p [ k ] })

-- Functor laws
μMor'Id : (P Q : SemCode κ) {i : Size} {x : muObj' P Q i} → muMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {const x} = cong const (MorId X)
μMor'Id P I {i}{rec x} = cong rec (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x , y} = cong₂ _,_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{in₁ x} = cong in₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{in₂ x} = cong in₂ (μMor'Id P R)
μMor'Id P (▸ Q) {i}{later x p} = cong₂-dep later refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))

μMor'Comp : (P Q : SemCode κ) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : muObj' P Q i}
  → muMor' P Q i k x ≡ muMor' P Q j k (muMor' P Q i j x)
μMor'Comp P (∁ X) {x = const x} = cong const (MorComp X)
μMor'Comp P I {x = rec x} = cong rec (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x , y} = cong₂ _,_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = in₁ x} = cong in₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = in₂ x} = cong in₂ (μMor'Comp P R)
μMor'Comp P (▸ Q) {x = later x p} = cong₂-dep later refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))

-- Semantic μ-types in the κ clock context
μ-κ : SemCode κ → SemCode κ → SemTy κ
μ-κ P Q = record
  { Obj = muObj' P Q
  ; Mor = muMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }

-- Semantic μ-types
mu : ∀ {Δ} → (P : SemCode Δ) → SemTy Δ
mu {κ} P = μ-κ P P
mu {∅} P = μset P P

