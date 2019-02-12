
module Prelude.Streams where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Prelude.Syntax

-- Destructor of elements of μ-types, inverse of cons
decons : ∀ {Δ} {Γ : Ctx Δ} {P : Code Δ} → Tm Γ (μ P) → Tm Γ (eval P (μ P))
decons {Γ = Γ} {P} = _$_ (primrec P (Pmap P (lambda (π₁ (var Γ (μ P ⊠ eval P (μ P))))))) 

-- Guarded streams
g-Str : Ty ∅ → Ty κ
g-Str A = μ (∁ (⇡ A) ⊠ ▻ I)

-- Head and tail of a guarded stream
g-hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ) (g-Str A) → Tm Γ A
g-hd {Γ}{A} xs = down (π₁ (decons xs))

g-tl : {Γ : Ctx κ} {A : Ty ∅} → Tm Γ (g-Str A) → Tm Γ (▻ (g-Str A))
g-tl {Γ}{A} xs = π₂ (decons xs)

-- Streams
Str : Ty ∅ → Ty ∅
Str A = □ (g-Str A)

-- Head and tail of a stream
hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ A
hd xs = g-hd (unbox xs)

tl : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
tl xs = force (box (g-tl (unbox xs)))

-- The constant guarded stream over a given element
g-const : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (⇡ Γ) (g-Str A)
g-const a = fix (lambda (cons _ [ wk (up a) & var _ _ ]))

const-str : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm Γ (Str A)
const-str a = box (g-const a)

-- A function removing the elements at even indices out of a given stream
-- This definition follows closely Mogelberg's definition in:
-- "A type theory for productive coprogramming via guarded recursion" LICS-CSL 2014
weakenSΓ : {Δ : ClockCtx} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Sub (Γ , A) (Γ , B)
weakenSΓ {_} {Γ} {A} {B} s = pr (id (Γ , A)) , app s

pfix-tm : {Γ : Ctx κ} {A B : Ty κ}
  → Tm (Γ , (A ⟶ ▻ B)) (A ⟶ B) → Tm Γ (A ⟶ B)
pfix-tm {Γ}{A}{B} f = fix (lambda (sub f (weakenSΓ (lambda (lambda (sub (var Γ (▻ (A ⟶ B))) (pr (id ((Γ , ▻ (A ⟶ B)) , A))) ⊛ next (var (Γ , ▻ (A ⟶ B)) A)))))))

oddrec : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ , (⇡ (Str A) ⟶ ▻ (g-Str A))) (⇡ (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,⇡ _ _ ∘ upA _ (pr (id _))
      f = wk (var _ _)
      xs = var _ _
  in
  lambda (cons _ [ sub (up (hd xs)) s & f $ (sub (up (tl xs)) s) ])

odd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
odd xs = box ((pfix-tm oddrec) $ (up xs))

