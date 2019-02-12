
module Prelude.Syntax where

open import Level
open import Function hiding (_$_; id; _∘_)
open import Data.Empty

-- Clock context
data ClockCtx : Set where
  ∅ κ : ClockCtx

-- Types
mutual
  data Ty : ClockCtx → Set where
    𝟙 : Ty ∅
    _⊠_ _⊞_ _⟶_ : ∀ {Δ} → Ty Δ → Ty Δ → Ty Δ
    ▻ : Ty κ → Ty κ
    □ : Ty κ → Ty ∅
    ⇡ : Ty ∅ → Ty κ
    μ : ∀ {Δ} → Code Δ → Ty Δ

-- Codes for functors
  data Code : ClockCtx → Set where
    ∁ : ∀ {Δ} → Ty Δ → Code Δ
    I : ∀ {Δ} → Code Δ
    _⊠_ _⊞_ : ∀ {Δ} → Code Δ → Code Δ → Code Δ
    ▻ : Code κ → Code κ

-- Code weakening
weakenP : Code ∅ → Code κ
weakenP (∁ X) = ∁ (⇡ X)
weakenP I = I
weakenP (P ⊞ Q) = weakenP P ⊞ weakenP Q
weakenP (P ⊠ Q) = weakenP P ⊠ weakenP Q

-- Evaluation of codes into functors on types
eval : ∀ {Δ} → Code Δ → Ty Δ → Ty Δ
eval (∁ Y) X = Y
eval I X = X
eval (P ⊞ Q) X = eval P X ⊞ eval Q X
eval (P ⊠ Q) X = eval P X ⊠ eval Q X
eval (▻ P) X = ▻ (eval P X)

-- Variable contexts
data Ctx : ClockCtx → Set where
  • : ∀ {Δ} → Ctx Δ
  _,_ : ∀ {Δ} → Ctx Δ → Ty Δ → Ctx Δ
  ⇡ : Ctx ∅ → Ctx κ

-- Terms
mutual
  data Tm : ∀ {Δ} → Ctx Δ → Ty Δ → Set where
-- -- Variables and substitutions  
    var : ∀ {Δ} (Γ : Ctx Δ) (A : Ty Δ) → Tm (Γ , A) A
    sub : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Tm Γ₂ A → Sub Γ₁ Γ₂ → Tm Γ₁ A

-- -- Introduction and elimination rules for function types, guarded recursive
-- -- types, products, coproducts and unit type    
    lambda : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm (Γ , A) B → Tm Γ (A ⟶ B)
    app : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Tm (Γ , A) B
    cons : ∀ {Δ} {Γ : Ctx Δ} (P : Code Δ) → Tm Γ (eval P (μ P)) → Tm Γ (μ P)
    primrec : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A : Ty Δ}
      → Tm Γ (eval P (μ P ⊠ A) ⟶ A) → Tm Γ (μ P ⟶ A)
    [_&_] : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ A → Tm Γ B → Tm Γ (A ⊠ B)
    π₁ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⊠ B) → Tm Γ A
    π₂ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⊠ B) → Tm Γ B
    tt : {Γ : Ctx ∅} → Tm Γ 𝟙
    unit-rec : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (Γ , 𝟙) A
    in₁ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} (B : Ty Δ) → Tm Γ A → Tm Γ (A ⊞ B)
    in₂ : ∀ {Δ} {Γ : Ctx Δ} (A : Ty Δ) {B : Ty Δ} → Tm Γ B → Tm Γ (A ⊞ B)
    ⊞rec : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (C : Ty Δ)
      → Tm (Γ , A) C → Tm (Γ , B) C → Tm (Γ , (A ⊞ B)) C

-- -- Applicative functor structure for ▻
    next : {Γ : Ctx κ} {A : Ty κ} → Tm Γ A → Tm Γ (▻ A)
    _⊛_ : {Γ : Ctx κ} {A B : Ty κ} → Tm Γ (▻ (A ⟶ B))
      → Tm Γ (▻ A) → Tm Γ (▻ B)

-- -- Delayed fixed point combinator
    dfix : {Γ : Ctx κ} {A : Ty κ} → Tm Γ (▻ A ⟶ A) → Tm Γ (▻ A)

-- -- Introduction and elimination rules for □
    box : {Γ : Ctx ∅} {A : Ty κ} → Tm (⇡ Γ) A → Tm Γ (□ A)
    unbox : {Γ : Ctx ∅} {A : Ty κ} → Tm Γ (□ A) → Tm (⇡ Γ) A

-- -- Force operation
    force : {Γ : Ctx ∅} {A : Ty κ} → Tm Γ (□ (▻ A)) → Tm Γ (□ A)

-- -- Introduction and elimination rule for type weakening
    up : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (⇡ Γ) (⇡ A)
    down : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ) (⇡ A) → Tm Γ A

-- -- Terms underlying type isomorphisms
    □const : {Γ : Ctx ∅} (A : Ty ∅) → Tm Γ (□ (⇡ A) ⟶ A)
    □sum : {Γ : Ctx ∅} (A B : Ty κ)
      → Tm Γ (□ (A ⊞ B) ⟶ (□ A ⊞ □ B))
    ⟶weaken : (A B : Ty ∅)
      → Tm • (((⇡ A) ⟶ (⇡ B)) ⟶ ⇡(A ⟶ B))
    μweaken : (P : Code ∅) → Tm • (⇡ (μ P) ⟶ μ (weakenP P))
    weakenμ : (P : Code ∅) → Tm • (μ (weakenP P) ⟶ ⇡ (μ P))

-- Explicit substitutions
  data Sub : ∀ {Δ} → Ctx Δ → Ctx Δ → Set where
-- -- Identity and composition of substitutions, the empty substitution,
-- -- the extension with an additional term, and the projection which
-- -- forgets the last term.  
    ε : ∀ {Δ} (Γ : Ctx Δ) → Sub Γ •
    id : ∀ {Δ} (Γ : Ctx Δ) → Sub Γ Γ
    _,_ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Sub Γ₁ Γ₂ → Tm Γ₁ A → Sub Γ₁ (Γ₂ , A)
    _∘_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₂ → Sub Γ₁ Γ₃
    pr : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Sub Γ₁ (Γ₂ , A) → Sub Γ₁ Γ₂

-- -- Embedding substitutions between ∅-contexts into substitutions
-- -- between κ-contexts
    up : {Γ₁ Γ₂ : Ctx ∅} → Sub Γ₁ Γ₂ → Sub (⇡ Γ₁) (⇡ Γ₂)
    down : {Γ₁ Γ₂ : Ctx ∅} → Sub (⇡ Γ₁) (⇡ Γ₂) → Sub Γ₁ Γ₂

-- -- Substitutions underlying context isomorphisms
    •⇡ : Sub • (⇡ •)
    ,⇡ : (Γ : Ctx ∅) (A : Ty ∅) → Sub (⇡ Γ , ⇡ A) (⇡ (Γ , A))


-- Derived operations on terms and substitutions
⇡• : Sub (⇡ •) •
⇡• = ε (⇡ •)

⇡, : (Γ : Ctx ∅) (A : Ty ∅) → Sub (⇡ (Γ , A)) (⇡ Γ , ⇡ A)
⇡, Γ A = up (pr (id (Γ , A))) , up (var Γ A)

upA : ∀ {Δ} {Γ Γ' : Ctx Δ} (A : Ty Δ) → Sub Γ Γ' → Sub (Γ , A) (Γ' , A)
upA {_} {Γ} {Γ'} A s = (s ∘ pr (id (Γ , A))) , var Γ A

wk  : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ B → Tm (Γ , A) B
wk x = sub x (pr (id (_ , _)))

_$_ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Tm Γ A → Tm Γ B
_$_ {_} {Γ} {A} {B} f x = sub (app f) (id Γ , x)

idmap : ∀ {Δ} {Γ : Ctx Δ} (A : Ty Δ) → Tm Γ (A ⟶ A)
idmap {_} {Γ} A = lambda (var Γ A)

⊞map : ∀ {Δ} {Γ : Ctx Δ} {A₁ B₁ A₂ B₂ : Ty Δ}
  → Tm Γ (A₁ ⟶ A₂) → Tm Γ (B₁ ⟶ B₂) → Tm Γ ((A₁ ⊞ B₁) ⟶ (A₂ ⊞ B₂))
⊞map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambda (⊞rec (A₂ ⊞ B₂)
                 (in₁ B₂ ((wk f) $ (var Γ A₁)))
                 (in₂ A₂ ((wk g) $ (var Γ B₁))))

⊠map : ∀ {Δ} {Γ : Ctx Δ} {A₁ B₁ A₂ B₂ : Ty Δ}
  → Tm Γ (A₁ ⟶ A₂) → Tm Γ (B₁ ⟶ B₂) → Tm Γ ((A₁ ⊠ B₁) ⟶ (A₂ ⊠ B₂))
⊠map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambda [ (wk f) $ (π₁ (var Γ (A₁ ⊠ B₁)))
           & (wk g) $ (π₂ (var Γ (A₁ ⊠ B₁))) ]

pairmap : ∀ {Δ} {Γ : Ctx Δ} {A B₁ B₂ : Ty Δ}
  → Tm Γ (A ⟶ B₁) → Tm Γ (A ⟶ B₂) → Tm Γ (A ⟶ (B₁ ⊠ B₂))
pairmap {Δ} {Γ} {A} {B₁} {B₂} f g  = lambda [ app f & app g ]

▻Pmap : {Γ : Ctx κ} {A B : Ty κ}
  → Tm Γ (A ⟶ B) → Tm Γ (▻ A ⟶ ▻ B)
▻Pmap {Γ} {A} {B} f =
  lambda (wk (next f) ⊛ var Γ (▻ A))

Pmap : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A B : Ty Δ}
  → Tm Γ (A ⟶ B) → Tm Γ (eval P A ⟶ eval P B)
Pmap (∁ X) f = idmap X
Pmap I f = f
Pmap (P ⊞ Q) f = ⊞map (Pmap P f) (Pmap Q f)
Pmap (P ⊠ Q) f = ⊠map (Pmap P f) (Pmap Q f)
Pmap (▻ P) f = ▻Pmap (Pmap P f)

compmap : ∀ {Δ} {Γ : Ctx Δ} {A B C : Ty Δ} → Tm Γ ((B ⟶ C) ⟶ ((A ⟶ B) ⟶ (A ⟶ C)))
compmap {_} {Γ} {A} {B} {C} =
  lambda
    (lambda
      (lambda
        ((wk (wk (var _ _))) $
          ((wk (var _ _)) $
            (var _ _)))))

□functor : {Γ : Ctx ∅} {A B : Ty κ} → Tm (⇡ Γ) (A ⟶ B) → Tm Γ (□ A) → Tm Γ (□ B)
□functor f t = box (f $ (unbox t))

const□ : {Γ : Ctx ∅} (A : Ty ∅) → Tm Γ (A ⟶ □ (⇡ A))
const□ {Γ} A = lambda (box (sub (var (⇡ Γ) (⇡ A)) (⇡, Γ A)))

sum□ : {Γ : Ctx ∅} (A B : Ty κ) → Tm Γ ((□ A ⊞ □ B) ⟶ □ (A ⊞ B))
sum□ A B = lambda
             (⊞rec (□ (A ⊞ B))
                   (□functor (lambda (in₁ B (var _ _))) (var _ _))
                   (□functor (lambda (in₂ A (var _ _))) (var _ _)))

□next : {Γ : Ctx ∅} {A : Ty κ} → Tm Γ (□ A) → Tm Γ (□(▻ A))
□next t = box (next (unbox t))

⊞weaken : (A B : Ty ∅) → Tm • (((⇡ A) ⊞ (⇡ B)) ⟶ ⇡(A ⊞ B))
⊞weaken A B = lambda
                (⊞rec (⇡ (A ⊞ B))
                      (sub (up (in₁ B (var _ _))) (,⇡ • A ∘ upA (⇡ A) •⇡))
                      (sub (up (in₂ A (var _ _))) (,⇡ • B ∘ upA (⇡ B) •⇡)))

help-weaken⊞ : (A B : Ty ∅) → Tm • ((A ⊞ B) ⟶ □(⇡ A ⊞ ⇡ B))
help-weaken⊞ A B = lambda ((sum□ (⇡ A) (⇡ B)) $
                             (⊞rec (□ (⇡ A) ⊞ □ (⇡ B))
                                   (in₁ (□ (⇡ B)) (box (sub (var (⇡ •) _) (⇡, • A))))
                                   (in₂ (□ (⇡ A)) (box (sub (var (⇡ •) _) (⇡, • B))))))

□-adj₁ : (A : Ty ∅) (B : Ty κ) → Tm • (⇡ A ⟶ B) → Tm • (A ⟶ □ B)
□-adj₁ A B t = lambda (box
                              ((sub (wk (sub t (ε (⇡ •))))
                                     (⇡, • A)) $
                                (up (var _ _))))

□-adj₂ : (A : Ty ∅) (B : Ty κ) → Tm • (A ⟶ □ B) → Tm • (⇡ A ⟶ B)
□-adj₂ A B t = lambda (sub (unbox ((wk t) $ (var _ _)))
                                   (,⇡ • A ∘ upA (⇡ A) •⇡))

weaken⊞ : (A B : Ty ∅) → Tm • (⇡(A ⊞ B) ⟶ ((⇡ A) ⊞ (⇡ B)))
weaken⊞ A B = □-adj₂ (A ⊞ B) (⇡ A ⊞ ⇡ B) (help-weaken⊞ A B)

split-prod : ∀ {Δ} (Γ : Ctx Δ) (A B C : Ty Δ)
  → Tm ((Γ , A) , B) C → Tm (Γ , (A ⊠ B)) C
split-prod Γ A B C t = sub t ((pr (id (Γ , (A ⊠ B))) , π₁ (var _ _)) , π₂ (var _ _))

⊠weaken : (A B : Ty ∅) → Tm • (((⇡ A) ⊠ (⇡ B)) ⟶ ⇡(A ⊠ B))
⊠weaken A B = lambda (split-prod • (⇡ A) (⇡ B) (⇡(A ⊠ B))
                                   (sub (up [ wk (var _ _) & var _ _ ])
                                        (,⇡ (• , A) B ∘ upA (⇡ B) (,⇡ • A ∘ upA (⇡ A) •⇡))))

weaken⊠ : (A B : Ty ∅) → Tm • (⇡(A ⊠ B) ⟶ ((⇡ A) ⊠ (⇡ B)))
weaken⊠ A B = lambda [ sub (up (π₁ (var • (A ⊠ B)))) (,⇡ • (A ⊠ B) ∘ upA (⇡ (A ⊠ B)) •⇡)
                       & sub (up (π₂ (var • (A ⊠ B)))) (,⇡ • (A ⊠ B) ∘ upA (⇡ (A ⊠ B)) •⇡) ]

weaken⟶ : (A B : Ty ∅) → Tm • (⇡(A ⟶ B) ⟶ ((⇡ A) ⟶ (⇡ B)))
weaken⟶ A B =
  lambda (lambda
           (sub (up ((wk (var • (A ⟶ B))) $ (var (• , (A ⟶ B)) A)))
                (,⇡ (• , (A ⟶ B)) A ∘ upA (⇡ A) (,⇡ • (A ⟶ B) ∘ upA (⇡ (A ⟶ B)) •⇡))))

fix : {Γ : Ctx κ} {A : Ty κ} → Tm Γ (▻ A ⟶ A) → Tm Γ A
fix f = f $ dfix f


infix 13 _∼_ _≈_

-- Definitional equality of terms
mutual
  data _∼_ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → Tm Γ A → Set where
-- -- Equivalence rules
    refl∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t : Tm Γ A} → t ∼ t
    sym∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → t₂ ∼ t₁
    trans∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t₁ t₂ t₃ : Tm Γ A} → t₁ ∼ t₂ → t₂ ∼ t₃ → t₁ ∼ t₃

-- -- Congruence rules
    cong-sub : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {t₁ t₂ : Tm Γ' A} {s₁ s₂ : Sub Γ Γ'} → t₁ ∼ t₂ → s₁ ≈ s₂ → sub t₁ s₁ ∼ sub t₂ s₂
    cong-unit-rec  : {Γ : Ctx ∅} {A : Ty ∅} {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → unit-rec t₁ ∼ unit-rec t₂
    cong-in₁ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} (B : Ty Δ) {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → in₁ A t₁ ∼ in₁ A t₂
    cong-in₂ : ∀ {Δ} {Γ : Ctx Δ} (A : Ty Δ) {B : Ty Δ} {t₁ t₂ : Tm Γ B} → t₁ ∼ t₂ → in₂ B t₁ ∼ in₂ B t₂
    cong-⊞rec : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (C : Ty Δ) {t₁ t₂ : Tm (Γ , A) C} {u₁ u₂ : Tm (Γ , B) C}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → ⊞rec C t₁ u₁ ∼ ⊞rec C t₂ u₂
    cong-[_&_] : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} {t₁ t₂ : Tm Γ A} {u₁ u₂ : Tm Γ B}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → [ t₁ & u₁ ] ∼ [ t₂ & u₂ ]
    cong-π₁ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} {t₁ t₂ : Tm Γ (A ⊠ B)} → t₁ ∼ t₂ → π₁ t₁ ∼ π₁ t₂
    cong-π₂ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} {t₁ t₂ : Tm Γ (A ⊠ B)} → t₁ ∼ t₂ → π₂ t₁ ∼ π₂ t₂
    cong-lambda : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} {t₁ t₂ : Tm (Γ , A) B} → t₁ ∼ t₂ → lambda t₁ ∼ lambda t₂
    cong-app  : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} {t₁ t₂ : Tm Γ (A ⟶ B)} → t₁ ∼ t₂ → app t₁ ∼ app t₂
    cong-up : {Γ : Ctx ∅} {A : Ty ∅} {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → up t₁ ∼ up t₂
    cong-down : {Γ : Ctx ∅} {A : Ty ∅} {t₁ t₂ : Tm (⇡ Γ) (⇡ A)} → t₁ ∼ t₂ → down t₁ ∼ down t₂
    cong-box : {Γ : Ctx ∅} {A : Ty κ} {t₁ t₂ : Tm (⇡ Γ) A} → t₁ ∼ t₂ → box t₁ ∼ box t₂
    cong-unbox : {Γ : Ctx ∅} {A : Ty κ} {t₁ t₂ : Tm Γ (□ A)} → t₁ ∼ t₂ → unbox t₁ ∼ unbox t₂
    cong-next : {Γ : Ctx κ} {A : Ty κ} {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → next t₁ ∼ next t₂
    cong-_⊛_ : {Γ : Ctx κ} {A B : Ty κ} {t₁ t₂ : Tm Γ (▻ (A ⟶ B))} {u₁ u₂ : Tm Γ (▻ A)} → t₁ ∼ t₂ → u₁ ∼ u₂ → t₁ ⊛ u₁ ∼ t₂ ⊛ u₂
    cong-dfix  : {Γ : Ctx κ} {A : Ty κ} {t₁ t₂ : Tm Γ (▻ A ⟶ A)} → t₁ ∼ t₂ → dfix t₁ ∼ dfix t₂
    cong-force : {Γ : Ctx ∅} {A : Ty κ} {t₁ t₂ : Tm Γ (□(▻ A))} → t₁ ∼ t₂ → force t₁ ∼ force t₂
    cong-cons : ∀ {Δ} {Γ : Ctx Δ} {P : Code Δ} {t₁ t₂ : Tm Γ (eval P (μ P))} → t₁ ∼ t₂ → cons P t₁ ∼ cons P t₂
    cong-primrec : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A : Ty Δ} {t₁ t₂ : Tm Γ (eval P (μ P ⊠ A) ⟶ A)}
      → t₁ ∼ t₂ → primrec P t₁ ∼ primrec P t₂

-- -- Beta and eta rules
    λ-β : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (t : Tm (Γ , A) B) → app (lambda t) ∼ t
    λ-η : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (t : Tm Γ (A ⟶ B)) → lambda (app t) ∼ t
    ⊠-β₁ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (t₁ : Tm Γ A) (t₂ : Tm Γ B) → π₁ [ t₁ & t₂ ] ∼ t₁
    ⊠-β₂ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (t₁ : Tm Γ A) (t₂ : Tm Γ B) → π₂ [ t₁ & t₂ ] ∼ t₂
    ⊠-η : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (t : Tm Γ (A ⊠ B)) → [ π₁ t & π₂ t ] ∼ t
    ⊞-β₁ : ∀ {Δ} {Γ : Ctx Δ} {A B C : Ty Δ} (l : Tm (Γ , A) C) (r : Tm (Γ , B) C) (t : Tm Γ A)
        → sub (⊞rec C l r) (id Γ , in₁ B t) ∼ sub l (id Γ , t)
    ⊞-β₂ : ∀ {Δ} {Γ : Ctx Δ} {A B C : Ty Δ} (l : Tm (Γ , A) C) (r : Tm (Γ , B) C) (t : Tm Γ B)
        → sub (⊞rec C l r) (id Γ , in₂ A t) ∼ sub r (id Γ , t)
    𝟙-β : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm Γ A) → sub (unit-rec t) (id Γ , tt) ∼ t
    𝟙-η : {Γ : Ctx ∅} (t : Tm Γ 𝟙) → t ∼ tt
    □-β : ∀ {Γ} {A} (t : Tm (⇡ Γ) A) → unbox (box t) ∼ t
    □-η : ∀ {Γ} {A} (t : Tm Γ (□ A)) → box (unbox t) ∼ t
    up-β : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm Γ A) → down (up t) ∼ t
    up-η : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ) (⇡ A)) → up (down t) ∼ t
    primrec-cons : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A : Ty Δ} (t : Tm Γ (eval P (μ P ⊠ A) ⟶ A)) (a : Tm Γ (eval P (μ P)))
      → (primrec P t) $ (cons P a) ∼ t $ ((Pmap P (pairmap (idmap (μ P)) (primrec P t))) $ a)

-- -- Applicative functor laws for ▻
    next-id : {Γ : Ctx κ} {A : Ty κ} (t : Tm Γ (▻ A)) → next (idmap A) ⊛ t ∼ t
    next-comp : {Γ : Ctx κ} {A B C : Ty κ} (g : Tm Γ (▻ (B ⟶ C))) (f : Tm Γ (▻ (A ⟶ B))) (t : Tm Γ (▻ A))
      → ((next compmap ⊛ g) ⊛ f) ⊛ t ∼ g ⊛ (f ⊛ t)
    next-⊛ : {Γ : Ctx κ} {A B : Ty κ} (f : Tm Γ (A ⟶ B)) (t : Tm Γ A) → next f ⊛ next t ∼ next (f $ t)
    next-λ : {Γ : Ctx κ} {A B : Ty κ} (f : Tm Γ (▻ (A ⟶ B))) (t : Tm Γ A)
      → f ⊛ next t ∼ next (lambda ((var _ _) $ (wk t))) ⊛ f

-- -- Fixpoint equations
    dfix-f : {Γ : Ctx κ} {A : Ty κ} (f : Tm Γ (▻ A ⟶ A)) → dfix f ∼ next (f $ dfix f) --f $ (next (fix f))
    dfix-u : {Γ : Ctx κ} {A : Ty κ} (f : Tm Γ (▻ A ⟶ A)) (u : Tm Γ (▻ A)) → next (f $ u) ∼ u → dfix f ∼ u

-- -- Substitutions laws
    sub-id : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} (t : Tm Γ A)
      → sub t (id Γ) ∼ t
    sub-sub : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Ty Δ} (t : Tm Γ₁ A) (s : Sub Γ₂ Γ₁) (s' : Sub Γ₃ Γ₂)
      → sub (sub t s) s' ∼ sub t (s ∘ s')
    sub-var : ∀ {Δ} (Γ₁ Γ₂ : Ctx Δ) (A : Ty Δ) (s : Sub Γ₂ Γ₁)
      → sub (var Γ₁ A) (upA A s) ∼ var Γ₂ A
    sub-unit-rec : {Γ₁ Γ₂ : Ctx ∅} {A : Ty ∅} (t : Tm Γ₁ A) (s : Sub Γ₂ Γ₁)
      → sub (unit-rec t) (upA 𝟙 s) ∼ unit-rec (sub t s)
    sub-in₁ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} (B : Ty Δ) (t : Tm Γ₁ A) (s : Sub Γ₂ Γ₁)
      → sub (in₁ B t) s ∼ in₁ B (sub t s)
    sub-in₂ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} (A : Ty Δ) {B : Ty Δ} (t : Tm Γ₁ B) (s : Sub Γ₂ Γ₁)
      → sub (in₂ B t) s ∼ in₂ B (sub t s)
    sub-[_&_] : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t₁ : Tm Γ₁ A) (t₂ : Tm Γ₁ B) (s : Sub Γ₂ Γ₁)
      → sub [ t₁ & t₂ ] s ∼ [ sub t₁ s & sub t₂ s ]
    sub-lambda : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm (Γ₁ , A) B) (s : Sub Γ₂ Γ₁)
      → sub (lambda t) s ∼ lambda (sub t (upA A s))
    sub-up : {Γ₁ Γ₂ : Ctx ∅} {A : Ty ∅} (t : Tm Γ₁ A) (s : Sub Γ₂ Γ₁)
      → sub (up t) (up s) ∼ up(sub t s)
    sub-box : {Γ₁ Γ₂ : Ctx ∅} {A : Ty κ} (t : Tm (⇡ Γ₁) A) (s : Sub Γ₂ Γ₁)
      → sub (box t) s ∼ box (sub t (up s))
    sub-next : {Γ₁ Γ₂ : Ctx κ} {A : Ty κ} (t : Tm Γ₁ A) (s : Sub Γ₂ Γ₁)
      → sub (next t) s ∼ next (sub t s)
    sub-⊛ : {Γ₁ Γ₂ : Ctx κ} {A B : Ty κ} (f : Tm Γ₁ (▻ (A ⟶ B))) (t : Tm Γ₁ (▻ A)) (s : Sub Γ₂ Γ₁)
      → sub (f ⊛ t) s ∼ (sub f s) ⊛ (sub t s)
    sub-dfix : {Γ₁ Γ₂ : Ctx κ} {A : Ty κ} (f : Tm Γ₁ (▻ A ⟶ A)) (s : Sub Γ₂ Γ₁)
      → sub (dfix f) s ∼ dfix (sub f s)
    sub-force : {Γ₁ Γ₂ : Ctx ∅} {A : Ty κ} (t : Tm Γ₁ (□(▻ A))) (s : Sub Γ₂ Γ₁)
      → sub (force t) s ∼ force (sub t s)
    sub-□const : {Γ₁ Γ₂ : Ctx ∅} (A : Ty ∅) (s : Sub Γ₂ Γ₁)
      → sub (□const A) s ∼ □const A
    sub-□sum : {Γ₁ Γ₂ : Ctx ∅} (A B : Ty κ) (s : Sub Γ₂ Γ₁)
      → sub (□sum A B) s ∼ □sum A B
    sub-cons : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {P : Code Δ} (t : Tm Γ₁ (eval P (μ P))) (s : Sub Γ₂ Γ₁)
      → sub (cons P t) s ∼ cons P (sub t s)
    sub-primrec : ∀ {Δ} (P : Code Δ) {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} (t : Tm Γ₁ (eval P (μ P ⊠ A) ⟶ A)) (s : Sub Γ₂ Γ₁)
      → sub (primrec P t) s ∼ primrec P (sub t s)

-- -- Type isomorphism equalities
    const□const : ∀ {Γ} {A} (t : Tm Γ (□ (⇡ A))) → const□ A $ (□const A $ t) ∼ t
    □const□ : ∀ {Γ} {A} (t : Tm Γ A) → □const A $ (const□ A $ t) ∼ t
    □sum□ : {Γ : Ctx ∅} (A B : Ty κ) (t : Tm Γ (□ A ⊞ □ B))
      → (□sum A B) $ ((sum□ A B) $ t) ∼ t
    sum□sum : {Γ : Ctx ∅} (A B : Ty κ) (t : Tm Γ (□ (A ⊞ B)))
      → (sum□ A B) $ ((□sum A B) $ t) ∼ t
    force-□next : {Γ : Ctx ∅} {A : Ty κ} (t : Tm Γ (□ A))
      → force(□next t) ∼ t
    □next-force : {Γ : Ctx ∅} {A : Ty κ} (t : Tm Γ (□ (▻ A)))
      → □next(force t) ∼ t
    ⟶weaken⟶ : (A B : Ty ∅) (t : Tm • (⇡ (A ⟶ B)))
      → (⟶weaken A B) $ ((weaken⟶ A B) $ t) ∼ t
    weaken⟶weaken : (A B : Ty ∅) (t : Tm • (⇡ A ⟶ ⇡ B))
      → (weaken⟶ A B) $ ((⟶weaken A B) $ t) ∼ t
    μweakenμ : (P : Code ∅) (t : Tm • (μ (weakenP P)))
      → (μweaken P) $ ((weakenμ P) $ t) ∼ t
    weakenμweaken : (P : Code ∅) (t : Tm • (⇡ (μ P)))
      → (weakenμ P) $ ((μweaken P) $ t) ∼ t

-- -- Equalities describing the relationship between the weakening operations
-- -- up and down and other term constructors
    updown : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ) (⇡ A)) → up(down t) ∼ t
    downup : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm Γ A) → down(up t) ∼ t
    upvar : (Γ : Ctx ∅) (A : Ty ∅) → up(var Γ A) ∼ sub (var (⇡ Γ) (⇡ A)) (⇡, Γ A)
    downvar : (Γ : Ctx ∅) (A : Ty ∅) → down(sub (var (⇡ Γ) (⇡ A)) (⇡, Γ A)) ∼ var Γ A
    upsub : {Γ Γ' : Ctx ∅} {A : Ty ∅} (t : Tm Γ' A) (s : Sub Γ Γ') → up(sub t s) ∼ sub (up t) (up s)
    downsub : {Γ Γ' : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ') (⇡ A)) (s : Sub Γ Γ') → down(sub t (up s)) ∼ sub (down t) s
    upπ₁ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm Γ (A ⊠ B)) → up(π₁ t) ∼ π₁ ((sub (weaken⊠ _ _) (ε (⇡ Γ))) $ (up t))
    upπ₂ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm Γ (A ⊠ B)) → up(π₂ t) ∼ π₂ ((sub (weaken⊠ _ _) (ε (⇡ Γ))) $ (up t))
    downπ₁ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm (⇡ Γ) (⇡ (A ⊠ B))) → π₁(down t) ∼ down(π₁((sub (weaken⊠ _ _) (ε (⇡ Γ))) $ t))
    downπ₂ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm (⇡ Γ) (⇡ (A ⊠ B))) → π₂(down t) ∼ down(π₂((sub (weaken⊠ _ _) (ε (⇡ Γ))) $ t))
    uppair : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t₁ : Tm Γ A) (t₂ : Tm Γ B) → up [ t₁ & t₂ ] ∼ (sub (⊠weaken _ _) (ε (⇡ Γ))) $ [ up t₁ & up t₂ ]
    downpair : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t₁ : Tm (⇡ Γ) (⇡ A)) (t₂ : Tm (⇡ Γ) (⇡ B))
      → [ down t₁ & down t₂ ] ∼ down ((sub (⊠weaken _ _) (ε (⇡ Γ))) $ [ t₁ & t₂ ])
    upin₁ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm Γ A) → up(in₁ B t) ∼ (sub (⊞weaken _ _) (ε (⇡ Γ))) $ (in₁ (⇡ B) (up t))
    upin₂ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm Γ B) → up(in₂ A t) ∼ (sub (⊞weaken _ _) (ε (⇡ Γ))) $ (in₂ (⇡ A) (up t))
    downin₁ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm (⇡ Γ) (⇡ A)) → in₁ B (down t) ∼ down((sub (⊞weaken _ _) (ε (⇡ Γ))) $ (in₁ (⇡ B) t))
    downin₂ : {Γ : Ctx ∅} {A : Ty ∅} {B : Ty ∅} (t : Tm (⇡ Γ) (⇡ B)) → in₂ A (down t) ∼ down((sub (⊞weaken _ _) (ε (⇡ Γ))) $ (in₂ (⇡ A) t))
    up⊞rec : {Γ : Ctx ∅} {A B : Ty ∅} (C : Ty ∅) (l : Tm (Γ , A) C) (r : Tm (Γ , B) C)
      → up(⊞rec C l r)
        ∼
        sub (⊞rec (⇡ C)
                  (sub (up l) (,⇡ Γ A))
                  (sub (up r) (,⇡ Γ B)))
            ((pr (id (⇡ Γ , ⇡ (A ⊞ B))) , ((sub (weaken⊞ _ _) (ε (⇡ Γ , ⇡ (A ⊞ B)))) $ (var (⇡ Γ) (⇡ (A ⊞ B))))) ∘ ⇡, Γ (A ⊞ B))
    down⊞rec : {Γ : Ctx ∅} {A B : Ty ∅} (C : Ty ∅) (l : Tm (⇡ (Γ , A)) (⇡ C)) (r : Tm (⇡ (Γ , B)) (⇡ C))
      → ⊞rec C (down l) (down r)
        ∼
        down (sub (⊞rec (⇡ C) (sub l (,⇡ Γ A)) (sub r (,⇡ Γ B)))
               (up (pr (id (Γ , (A ⊞ B)))) , ((sub (weaken⊞ _ _) (ε (⇡ (Γ , (A ⊞ B))))) $ (up (var Γ (A ⊞ B))))))
    uplambda : {Γ : Ctx ∅} {A B : Ty ∅} (t : Tm (Γ , A) B) → up (lambda t) ∼ (sub (⟶weaken _ _) (ε (⇡ Γ))) $ (lambda (sub (up t) (,⇡ Γ A)))
    downlambda : {Γ : Ctx ∅} {A B : Ty ∅} (t : Tm (⇡ (Γ , A)) (⇡ B)) → lambda (down t) ∼ down ((sub (⟶weaken _ _) (ε (⇡ Γ))) $ (lambda (sub t (,⇡ Γ A))))
    upapp : {Γ : Ctx ∅} {A B : Ty ∅} (t : Tm Γ (A ⟶ B)) → up (app t) ∼ sub (app ((sub (weaken⟶ _ _) (ε (⇡ Γ))) $ (up t))) (⇡, Γ A)
    downapp : {Γ : Ctx ∅} {A B : Ty ∅} (t : Tm (⇡ Γ) (⇡ (A ⟶ B))) → app (down t) ∼ down (sub (app ((sub (weaken⟶ _ _) (ε (⇡ Γ))) $ t)) (⇡, Γ A))

-- Definitional equality of substitutions
  data _≈_ : ∀ {Δ} {Γ Γ' : Ctx Δ} → Sub Γ Γ' → Sub Γ Γ' → Set where
-- -- Equivalence rules  
    refl≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s : Sub Γ Γ'} → s ≈ s
    sym≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s₁ s₂ : Sub Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₁
    trans≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s₁ s₂ s₃ : Sub Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃

-- -- Congruence rules
    cong-_,s_ : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {s₁ s₂ : Sub Γ Γ'} {t₁ t₂ : Tm Γ A} → s₁ ≈ s₂ → t₁ ∼ t₂ → s₁ , t₁ ≈ s₂ , t₂
    cong-_o_ : ∀ {Δ} {Γ Γ' Γ'' : Ctx Δ} {s₁ s₂ : Sub Γ' Γ''} {σ₁ σ₂ : Sub Γ Γ'} → s₁ ≈ s₂ → σ₁ ≈ σ₂ → s₁ ∘ σ₁ ≈ s₂ ∘ σ₂
    cong-pr : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {s₁ s₂ : Sub Γ (Γ' , A)} → s₁ ≈ s₂ → pr s₁ ≈ pr s₂
    cong-up : {Γ Γ' : Ctx ∅} {s₁ s₂ : Sub Γ Γ'} → s₁ ≈ s₂ → up s₁ ≈ up s₂
    cong-down : {Γ Γ' : Ctx ∅} {s₁ s₂ : Sub (⇡ Γ) (⇡ Γ')} → s₁ ≈ s₂ → down s₁ ≈ down s₂

-- -- Category and projection laws    
    sub-idl : ∀ {Δ} {Γ Γ' : Ctx Δ} (s : Sub Γ Γ') → id Γ' ∘ s ≈ s
    sub-idr : ∀ {Δ} {Γ Γ' : Ctx Δ} (s : Sub Γ Γ') → s ∘ id Γ ≈ s
    sub-assoc : ∀ {Δ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx Δ} (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃) (s₃ : Sub Γ₃ Γ₄)
      → s₃ ∘ (s₂ ∘ s₁) ≈ (s₃ ∘ s₂) ∘ s₁
    sub-π₁β : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {t : Tm Γ A} (s : Sub Γ Γ')
      → pr (s , t) ≈ s
    sub-εη : ∀ {Δ} {Γ : Ctx Δ} (s : Sub Γ •) → s ≈ ε Γ
    sub-,o : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Ty Δ} {t : Tm Γ₂ A} (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃)
      → (s₂ , t) ∘ s₁ ≈ (s₂ ∘ s₁) , sub t s₁
    sub-η : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} (s : Sub Γ (Γ , A))
      → pr s , sub (var Γ A) s ≈ s

-- -- Context isomorphism equalities
    •⇡-id : •⇡ ∘ ⇡• ≈ id (⇡ •)
    ⇡•-id : ⇡• ∘ •⇡ ≈ id •
    ,⇡-id : (Γ : Ctx ∅) (A : Ty ∅) → ,⇡ Γ A ∘ ⇡, Γ A ≈ id (⇡ (Γ , A))
    ⇡,-id : (Γ : Ctx ∅) (A : Ty ∅) → ⇡, Γ A ∘ ,⇡ Γ A ≈ id (⇡ Γ , ⇡ A)

-- -- Equalities describing the relationship between the weakening operations
-- -- up and down and other substitution constructors
    updown : {Γ Γ' : Ctx ∅} (s : Sub (⇡ Γ) (⇡ Γ')) → up (down s) ≈ s
    downup : {Γ Γ' : Ctx ∅} (s : Sub Γ Γ') → down (up s) ≈ s
    up-ε : (Γ : Ctx ∅) → up (ε Γ) ≈ (•⇡ ∘ ε (⇡ Γ))
    up-o : {Γ Γ' Γ'' : Ctx ∅} (s₁ : Sub Γ' Γ'') (s₂ : Sub Γ Γ') → up (s₁ ∘ s₂) ≈ (up s₁ ∘ up s₂)
    up-pr : {Γ Γ' : Ctx ∅} {A : Ty ∅} (s : Sub Γ (Γ' , A)) → up (pr s) ≈ pr (⇡, Γ' A ∘ up s)
    up-idsub : (Γ : Ctx ∅) → up (id Γ) ≈ id (⇡ Γ)
    up-,s : {Γ Γ' : Ctx ∅} {A : Ty ∅} (s : Sub Γ Γ') (t : Tm Γ A) → up (s , t) ≈ ,⇡ Γ' A ∘ (up s , up t)
    down-ε : (Γ : Ctx ∅) → down (•⇡ ∘ ε (⇡ Γ)) ≈ ε Γ
    down-o : {Γ Γ' Γ'' : Ctx ∅} (s₁ : Sub (⇡ Γ') (⇡ Γ'')) (s₂ : Sub (⇡ Γ) (⇡ Γ')) → down (s₁ ∘ s₂) ≈ (down s₁ ∘ down s₂)
    down-pr : {Γ Γ' : Ctx ∅} {A : Ty ∅} (s : Sub (⇡ Γ) (⇡ (Γ' , A))) → down (pr (⇡, Γ' A ∘ s)) ≈ pr (down s)
    down-idsub : (Γ : Ctx ∅) → down (id (⇡ Γ)) ≈ id Γ
    down-,s : {Γ Γ' : Ctx ∅} {A : Ty ∅} (s : Sub (⇡ Γ) (⇡ Γ')) (t : Tm (⇡ Γ) (⇡ A)) → down (,⇡ Γ' A ∘ (s , t)) ≈ (down s , down t)
