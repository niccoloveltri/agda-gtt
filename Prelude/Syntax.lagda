\AgdaHide{
\begin{code}
module Prelude.Syntax where

open import Level
open import Function hiding (_$_; id; _∘_)
open import Data.Empty
\end{code}
}

The object language we consider is simply typed lambda calculus
extended with additional features for programming with guarded recursive and coinductive
types. We call this language \GTT. It is a variant of Atkey and McBride's type system %, which we call \AM,
for
productive coprogramming \cite{atkey2013productive}. In Atkey and McBride's calculus, all judgments are indexed by a clock context,
which may contain several different clocks. They extend simply typed
lambda calculus with two additional type formers: a modality ▻ for
encoding time delay into types and universal quantification over clock
variables ∀, which is used in combination with ▻ to specify coinductive types.

\GTT\ is a type theory with explicit substitutions \cite{AbadiCCL91}. It comprises
well-formed types and contexts, well-typed terms and substitutions,
definitional equality of terms and of substitutions. All of them depend on a clock context.
In \GTT, the clock context can either be empty or contain a single clock \IC{κ}.

%% We now give a description of the object type theory. This is a simple
%% type theory with guarded recursion that can be seen as a variant of
%% Atkey and McBride's type system \cite{atkey2013productive} but
%% allowing the presence of at most one clock in context.
%% In Atkey and McBride's system, judgements are parametrized by a clock
%% context. In our case, the clock context can either be empty or contain
%% a single clock \IC{κ}.
\begin{code}
data ClockCtx : Set where
  ∅ κ : ClockCtx
\end{code}
%% Moreover we employ explicit substitutions \cite{AbadiCCL91}, so on top of the usual we
%% define four sorts
\AgdaHide{
\begin{code}
mutual
\end{code}
}
We refer to types and contexts in the empty clock context as \IC{∅}-types and
\IC{∅}-contexts respectively. Similarly,  \IC{κ}-types and
\IC{κ}-contexts are types and contexts depending on \IC{κ}.

\subsection{Types}

The well-formed types of \GTT\ include the unit type,
products, coproducts, and function spaces. Notice that \IC{𝟙} is a
\IC{∅}-type.
\begin{AgdaAlign}
\begin{code}
  data Ty : ClockCtx → Set where
    𝟙 : Ty ∅
    _⊠_ _⊞_ _⟶_ : ∀ {Δ} → Ty Δ → Ty Δ → Ty Δ
\end{code}

We include a modality \IC{▻} as an operation on \IC{κ}-types similar to the one in Atkey and McBride's system.
There is also a nameless analogue of clock quantification, which we call ``box'' and denote by \IC{□}
following \cite{CloustonBGB15}. The box modality takes a
\IC{κ}-type and returns a \IC{∅}-type. The well-formed types of \GTT\
include a weakening type former \IC{⇡}, which maps \IC{∅}-types to
\IC{κ}-types.
%% In addition to the usual simple type formers, there are types that
%% allow us to specify guarded recursive and coinductive types. We have
%% the later modality, which takes a type in the \IC{κ} clock context and
%% returns a type in the \IC{κ} clock context.
%% We have clock quantification, which takes a type in the \IC{κ} clock
%% context and returns a type in the \IC{∅} clock context. 
\begin{code}
    ▻ : Ty κ → Ty κ
    □ : Ty κ → Ty ∅
    ⇡ : Ty ∅ → Ty κ
\end{code}

Guarded recursive types are defined using a least fixpoint
type former \IC{μ}.
\begin{code}
    μ : ∀ {Δ} → Code Δ → Ty Δ
\end{code}
\end{AgdaAlign}
For \IC{μ} to be well-defined, one typically limits
its applicability to strictly positive functors. We instead consider
a grammar \F{Code} \Ar{Δ} for functors, which has codes for constant functors,
the identity, products, coproducts, and the later modality.
Since there is a code for constant functors, the type family
\F{Code} needs to be defined simultaneously with \F{Ty}.
%% The type \F{Code} \Ar{Δ} specifies a grammar for functors we allow 
%% The constructor \IC{μ} takes an element of \F{Code} and returnA guarded recursive type in a clock context \Ar{Δ} takes an element of
%% \F{Code} \Ar{Δ} as its input. We call these elements polynomials. 
\begin{code}
  data Code : ClockCtx → Set where
    ∁ : ∀ {Δ} → Ty Δ → Code Δ
    I : ∀ {Δ} → Code Δ
    _⊠_ _⊞_ : ∀ {Δ} → Code Δ → Code Δ → Code Δ
    ▻ : Code κ → Code κ
\end{code}
\AgdaHide{
\begin{code}
weakenP : Code ∅ → Code κ
weakenP (∁ X) = ∁ (⇡ X)
weakenP I = I
weakenP (P ⊞ Q) = weakenP P ⊞ weakenP Q
weakenP (P ⊠ Q) = weakenP P ⊠ weakenP Q
\end{code}
}
The constructors of \F{Code} \Ar{Δ} suffice for the specification of interesting examples of guarded recursive types such as streams. Nevertheless, it would not be complicated to add exponentials with
constant domain and the box modality to the grammar.
%% We associate to each code \Ar{P} in \F{Code} \Ar{Δ} a functor \F{eval}
%% \Ar{P} acting on \F{Ty} \Ar{Δ} defined by induction on \Ar{P}.
%% Then \IC{μ} \Ar{P} is then the least fixed point of \F{eval} \Ar{P}. Notice that for this kind of fixed points to exist, one typically restricts the constructors of
%% the type family \F{Code} so that the functor \F{eval} \Ar{P} is
%% strictly positive, for all \Ar{P}.  Here we consider a grammar for
%% polynomials consisting of constant functors, the identity functor,
%% products, coproducts and the later modality. Exponentials with
%% constant domain and clock quantification could also be added to the
%% grammar, but we did not consider them in our formalization.


\AgdaHide{
\begin{code}
eval : ∀ {Δ} → Code Δ → Ty Δ → Ty Δ
eval (∁ Y) X = Y
eval I X = X
eval (P ⊞ Q) X = eval P X ⊞ eval Q X
eval (P ⊠ Q) X = eval P X ⊠ eval Q X
eval (▻ P) X = ▻ (eval P X)
\end{code}
}

\subsection{Contexts}
The well-formed contexts of \GTT\ are built from the empty context, context extension, and context weakening. The last operation embeds \IC{∅}-contexts into \IC{κ}-contexts. 
Notice that we are overloading the symbol \IC{⇡}, also used for type weakening.
\begin{AgdaAlign}
\begin{code}
data Ctx : ClockCtx → Set where
  • : ∀ {Δ} → Ctx Δ
  _,_ : ∀ {Δ} → Ctx Δ → Ty Δ → Ctx Δ
  ⇡ : Ctx ∅ → Ctx κ
\end{code}
\end{AgdaAlign}
%% In addition to the usual context formers, we have context
%% weakening. This operation takes a context in the \IC{∅} clock context
%% and returns a context in the \IC{κ} clock context. It is the context
%% analogue of the type former \IC{⇡}. Notice that we are overloading the
%% constructor \IC{⇡}.

\AgdaHide{
\begin{code}
mutual
\end{code}
}

\subsection{Terms}

The well-typed terms and substitutions of \GTT\ are defined simultaneously. Terms
include constructors for variables and substitutions.
\begin{AgdaAlign}
\begin{code}
  data Tm : ∀ {Δ} → Ctx Δ → Ty Δ → Set where
    var : ∀ {Δ} (Γ : Ctx Δ) (A : Ty Δ) → Tm (Γ , A) A
    sub : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Tm Γ₂ A → Sub Γ₁ Γ₂ → Tm Γ₁ A
\end{code}

We have lambda abstraction and application, plus the usual
introduction and elimination rules for the unit types, products, 
coproducts, and guarded recursive types. Here we only show the typing rules associated to function types and guarded recursive types.
The function \F{eval} evaluates codes in \F{Code} \Ar{Δ} into endofunctors on \F{Ty} \Ar{Δ}.
We use a categorical combinator \IC{app} for application.
The conventional application, which we call \F{\$}, taking additionally an element
in \F{Tm} \Ar{Γ} \Ar{A} and returning an inhabitant of \F{Tm} \Ar{Γ} \Ar{B}, is derivable.
\begin{code}
    lambda : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm (Γ , A) B → Tm Γ (A ⟶ B)
    app : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Tm (Γ , A) B
    cons : ∀ {Δ} {Γ : Ctx Δ} (P : Code Δ) → Tm Γ (eval P (μ P)) → Tm Γ (μ P)
    primrec : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A : Ty Δ}
      → Tm Γ (eval P (μ P ⊠ A) ⟶ A) → Tm Γ (μ P ⟶ A)
\end{code}
\AgdaHide{
\begin{code}
    [_&_] : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ A → Tm Γ B → Tm Γ (A ⊠ B)
    π₁ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⊠ B) → Tm Γ A
    π₂ : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⊠ B) → Tm Γ B
    tt : {Γ : Ctx ∅} → Tm Γ 𝟙
    unit-rec : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (Γ , 𝟙) A
    in₁ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} (B : Ty Δ) → Tm Γ A → Tm Γ (A ⊞ B)
    in₂ : ∀ {Δ} {Γ : Ctx Δ} (A : Ty Δ) {B : Ty Δ} → Tm Γ B → Tm Γ (A ⊞ B)
    ⊞rec : ∀ {Δ} {Γ : Ctx Δ} {A B : Ty Δ} (C : Ty Δ)
      → Tm (Γ , A) C → Tm (Γ , B) C → Tm (Γ , (A ⊞ B)) C
\end{code}
}

The later modality is required to be an applicative functor, which means that we have terms \IC{next} and \IC{⊛}.
The delayed fixpoint combinator \IC{dfix} \cite{BahrGM17} allows defining productive recursive programs. The usual fixpoint returning a term in \Ar{A} instead of \IC{▻} \Ar{A} is derivable.
\begin{code}
    next : {Γ : Ctx κ} {A : Ty κ} → Tm Γ A → Tm Γ (▻ A)
    _⊛_ : {Γ : Ctx κ} {A B : Ty κ} → Tm Γ (▻ (A ⟶ B)) → Tm Γ (▻ A) → Tm Γ (▻ B)
    dfix : {Γ : Ctx κ} {A : Ty κ} → Tm Γ (▻ A ⟶ A) → Tm Γ (▻ A)
\end{code}
%     fix : {Γ : Ctx κ} {A : Ty κ} → Tm Γ (▻ A ⟶ A) → Tm Γ A

We have introduction and elimination
rules for the \IC{□} modality. The rule \IC{box} is the analogue in \GTT\ of 
Atkey and McBride's rule for clock abstraction
\cite{atkey2013productive}. Notice that \IC{box} can only be applied
to terms of type \Ar{A} over a weakened context \IC{⇡}
\Ar{Γ}. This is in analogy with Atkey and McBride's side condition
requiring the universally quantified clock variable to not appear free
in the context \Ar{Γ}. Similarly, the rule \IC{unbox} corresponds to
clock application. The operation \IC{force} is used for removing occurrences of \IC{▻} protected by the \IC{□} modality.
\begin{code}
    box : {Γ : Ctx ∅} {A : Ty κ} → Tm (⇡ Γ) A → Tm Γ (□ A)
    unbox : {Γ : Ctx ∅} {A : Ty κ} → Tm Γ (□ A) → Tm (⇡ Γ) A
    force : {Γ : Ctx ∅} {A : Ty κ} → Tm Γ (□ (▻ A)) → Tm Γ (□ A)
\end{code}

The introduction and elimination rules for type weakening say that
elements of \F{Tm} \Ar{Γ A} can be embedded in \F{Tm} (\IC{⇡}
\Ar{Γ}) (\IC{⇡} \Ar{A}) and vice versa.
\begin{code}
    up : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (⇡ Γ) (⇡ A)
    down : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ) (⇡ A) → Tm Γ A
\end{code}

Atkey and McBride assume the existence of certain type equalities
\cite{atkey2013productive}. M{\o}gelberg, who works in a dependently typed setting, considers similar type isomorphisms \cite{Mogelberg14}. In \GTT, we
follow the second approach. This means that we do not introduce an
equivalence relation on types specifying which types should be
considered equal, as in Chapman's object type theory
\cite{Chapman09}. Instead, we include additional term constructors
corresponding to functions underlying the required type
isomorphisms. For example, the clock irrelevance axiom formulated in our setting states that every \IC{∅}-type \Ar{A} is isomorphic to \IC{□} (\IC{⇡} \Ar{A}). This is obtained by adding to \AD{Tm} a constructor \IC{□const}.
\begin{code}
    □const : {Γ : Ctx ∅} (A : Ty ∅) → Tm Γ (□ (⇡ A) ⟶ A)
\end{code}
%in \F{Tm} \Ar{Γ} (\Ar{A} \IC{⟶} \IC{□} (\IC{⇡} \Ar{A}))
A function \F{const□} \Ar{A} in the other direction is derivable.
When defining definitional equality on terms, described in Section \ref{sec:defeq}, we
ask for \IC{□const} and \F{const□} to be each other inverses.
The other type isomorphisms are constructed in a similar way.
\AgdaHide{
\begin{code}
    □sum : {Γ : Ctx ∅} (A B : Ty κ)
      → Tm Γ (□ (A ⊞ B) ⟶ (□ A ⊞ □ B))
    ⟶weaken : (A B : Ty ∅)
      → Tm • (((⇡ A) ⟶ (⇡ B)) ⟶ ⇡(A ⟶ B))
    μweaken : (P : Code ∅) → Tm • (⇡ (μ P) ⟶ μ (weakenP P))
    weakenμ : (P : Code ∅) → Tm • (μ (weakenP P) ⟶ ⇡ (μ P))
\end{code}
}

\subsection{Substitutions}
For substitutions, we need the canonical necessary operations \cite{AltenkirchK16,Chapman09}: identity and composition of
substitutions, the empty substitution, the extension with an additional term, and the projection which forgets the last term.
\begin{code}
  data Sub : ∀ {Δ} → Ctx Δ → Ctx Δ → Set where
    ε : ∀ {Δ} (Γ : Ctx Δ) → Sub Γ •
    id : ∀ {Δ} (Γ : Ctx Δ) → Sub Γ Γ
    _,_ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Sub Γ₁ Γ₂ → Tm Γ₁ A → Sub Γ₁ (Γ₂ , A)
    _∘_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₂ → Sub Γ₁ Γ₃
    pr : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} → Sub Γ₁ (Γ₂ , A) → Sub Γ₁ Γ₂
\end{code}

We also add rules for embedding substitutions between \IC{∅}-contexts into substitutions between \IC{κ} contexts and vice versa.

\begin{code}
    up : {Γ₁ Γ₂ : Ctx ∅} → Sub Γ₁ Γ₂ → Sub (⇡ Γ₁) (⇡ Γ₂)
    down : {Γ₁ Γ₂ : Ctx ∅} → Sub (⇡ Γ₁) (⇡ Γ₂) → Sub Γ₁ Γ₂
\end{code}

In addition, we require the existence of two context isomorphisms. The context \IC{⇡ •} needs
to be isomorphic to \IC{•} and \IC{⇡} (\Ar{Γ} \IC{,} \Ar{A})
needs to be isomorphic to \IC{⇡} \Ar{Γ} \IC{,} \IC{⇡}
\Ar{A}. For both of them, we add a constructor representing the underlying functions.

\begin{code}
    •⇡ : Sub • (⇡ •)
    ,⇡ : (Γ : Ctx ∅) (A : Ty ∅) → Sub (⇡ Γ , ⇡ A) (⇡ (Γ , A))
\end{code}
\end{AgdaAlign}
An element \F{⇡•} in \F{Sub}
(\IC{⇡ •}) \IC{•} is derivable. In the definitional
equality on substitutions, we ask for \IC{•⇡} and
\F{⇡•} to be each other inverses. We proceed similarly with
\IC{,⇡}.

\AgdaHide{
\begin{code}
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

{-
subst-μ-help : ∀ {Δ} (Γ : Ctx Δ) (A B : Ty Δ)
  → Sub (Γ , (A ⊠ B)) (Γ , A)
subst-μ-help = {!!}

weaken-eval : {Γ : Ctx ∅} (P : Code ∅) (A : Ty ∅)
  → Tm (⇡ Γ) (⇡ (eval P A) ⟶ eval (weakenP P) (⇡ A))
weaken-eval {Γ} P A = lambda (sub (var (⇡ Γ) _) {!!})

weakenμ : (P : Code ∅) → Tm • (μ (weakenP P) ⟶ ⇡ (μ P))
weakenμ P =
  primrec (weakenP P)
          (lambda (sub (up (cons P (var • _)))
                         ((,⇡ • (eval P (μ P)) o
                           (upA (⇡ (eval P (μ P))) •⇡ o
                           {!!})) o
                           subst-μ-help • (eval (weakenP P) (μ (weakenP P))) (eval (weakenP P) (⇡ (μ P))))))
-}
infix 13 _∼_ _≈_
\end{code}
}

\subsection{Definitional equalities}
\label{sec:defeq}

Definitional equalities on terms and substitutions are defined simultaneously.
Here we only discuss equality on terms and we refer to the formalization for the equality on substitutions.
\AgdaHide{
\begin{code}
mutual
\end{code}
}
\begin{AgdaAlign}
\begin{code}
  data _∼_ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → Tm Γ A → Set where
\end{code}

The term equality includes rules for equivalence, congruence, and
substitution. There are also $\beta$ and $\eta$ rules for the type
formers. Among these rules, here we only show the ones associated to the
\IC{□} modality. The rules state that \IC{box} and \IC{unbox} are each
other's inverses.
%up to \AD{∼}.
\AgdaHide{
\begin{code}
    refl∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t : Tm Γ A} → t ∼ t
    sym∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t₁ t₂ : Tm Γ A} → t₁ ∼ t₂ → t₂ ∼ t₁
    trans∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t₁ t₂ t₃ : Tm Γ A} → t₁ ∼ t₂ → t₂ ∼ t₃ → t₁ ∼ t₃
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
\end{code}
}
\begin{code}
    □-β : ∀ {Γ} {A} (t : Tm (⇡ Γ) A) → unbox (box t) ∼ t
    □-η : ∀ {Γ} {A} (t : Tm Γ (□ A)) → box (unbox t) ∼ t
\end{code}

We include definitional equalities stating that \IC{▻} is an applicative functor \wrt the operations \IC{next} and \IC{⊛}.
Furthermore, the delayed fixpoint combinator \IC{dfix} must satisfy its characteristic unfolding equation.
%% There is also the
%% characteristic equality of the fixpoint combinator, stating that
%% \IC{fix} \Ar{f} is equal to the application of the function term
%% \Ar{f} to \IC{next} (\IC{fix} \Ar{f}).
We refer to M{\o}gelberg's paper \cite{Mogelberg14} for a complete list of the required definitional equalities for \IC{▻} and \IC{□}.
\AgdaHide{
\begin{code}
    up-β : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm Γ A) → down (up t) ∼ t
    up-η : {Γ : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ) (⇡ A)) → up (down t) ∼ t
    next-id : {Γ : Ctx κ} {A : Ty κ} (t : Tm Γ (▻ A)) → next (idmap A) ⊛ t ∼ t
    next-comp : {Γ : Ctx κ} {A B C : Ty κ} (g : Tm Γ (▻ (B ⟶ C))) (f : Tm Γ (▻ (A ⟶ B))) (t : Tm Γ (▻ A))
      → ((next compmap ⊛ g) ⊛ f) ⊛ t ∼ g ⊛ (f ⊛ t)
    next-⊛ : {Γ : Ctx κ} {A B : Ty κ} (f : Tm Γ (A ⟶ B)) (t : Tm Γ A) → next f ⊛ next t ∼ next (f $ t)
    next-λ : {Γ : Ctx κ} {A B : Ty κ} (f : Tm Γ (▻ (A ⟶ B))) (t : Tm Γ A)
      → f ⊛ next t ∼ next (lambda ((var _ _) $ (wk t))) ⊛ f
    dfix-f : {Γ : Ctx κ} {A : Ty κ} (f : Tm Γ (▻ A ⟶ A)) → dfix f ∼ next (f $ dfix f) --f $ (next (fix f))
    dfix-u : {Γ : Ctx κ} {A : Ty κ} (f : Tm Γ (▻ A ⟶ A)) (u : Tm Γ (▻ A)) → next (f $ u) ∼ u → dfix f ∼ u
    primrec-cons : ∀ {Δ} (P : Code Δ) {Γ : Ctx Δ} {A : Ty Δ} (t : Tm Γ (eval P (μ P ⊠ A) ⟶ A)) (a : Tm Γ (eval P (μ P)))
      → (primrec P t) $ (cons P a) ∼ t $ ((Pmap P (pairmap (idmap (μ P)) (primrec P t))) $ a)
      --app-map (primrec P t) (cons P a) ∼ app-map t [ a & app-map (Pmap P (primrec P t)) a ]
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
\end{code}
}

For the type isomorphisms, we require term equalities exhibiting that certain maps are mutual inverses.
For example, we have the following two equalities about \IC{□const} and \F{const□}:

\begin{code}
    const□const : ∀ {Γ} {A} (t : Tm Γ (□ (⇡ A))) → const□ A $ (□const A $ t) ∼ t
    □const□ : ∀ {Γ} {A} (t : Tm Γ A) → □const A $ (const□ A $ t) ∼ t
\end{code}

The last group of term equalities describes the relationship between the
weakening operations \IC{up} and \IC{down} and other term constructors. Here we omit their description and we refer the
interested reader to the Agda formalization.
\AgdaHide{
\begin{code}
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
\end{code}
}
\end{AgdaAlign}

\AgdaHide{
\begin{code}
  data _≈_ : ∀ {Δ} {Γ Γ' : Ctx Δ} → Sub Γ Γ' → Sub Γ Γ' → Set where -- ≈
    refl≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s : Sub Γ Γ'} → s ≈ s
    sym≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s₁ s₂ : Sub Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₁
    trans≈ : ∀ {Δ} {Γ Γ' : Ctx Δ} {s₁ s₂ s₃ : Sub Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
    cong-_,s_ : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {s₁ s₂ : Sub Γ Γ'} {t₁ t₂ : Tm Γ A} → s₁ ≈ s₂ → t₁ ∼ t₂ → s₁ , t₁ ≈ s₂ , t₂
    cong-_o_ : ∀ {Δ} {Γ Γ' Γ'' : Ctx Δ} {s₁ s₂ : Sub Γ' Γ''} {σ₁ σ₂ : Sub Γ Γ'} → s₁ ≈ s₂ → σ₁ ≈ σ₂ → s₁ ∘ σ₁ ≈ s₂ ∘ σ₂
    cong-pr : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Ty Δ} {s₁ s₂ : Sub Γ (Γ' , A)} → s₁ ≈ s₂ → pr s₁ ≈ pr s₂
    cong-up : {Γ Γ' : Ctx ∅} {s₁ s₂ : Sub Γ Γ'} → s₁ ≈ s₂ → up s₁ ≈ up s₂
    cong-down : {Γ Γ' : Ctx ∅} {s₁ s₂ : Sub (⇡ Γ) (⇡ Γ')} → s₁ ≈ s₂ → down s₁ ≈ down s₂
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
    •⇡-id : •⇡ ∘ ⇡• ≈ id (⇡ •)
    ⇡•-id : ⇡• ∘ •⇡ ≈ id •
    ,⇡-id : (Γ : Ctx ∅) (A : Ty ∅) → ,⇡ Γ A ∘ ⇡, Γ A ≈ id (⇡ (Γ , A))
    ⇡,-id : (Γ : Ctx ∅) (A : Ty ∅) → ⇡, Γ A ∘ ,⇡ Γ A ≈ id (⇡ Γ , ⇡ A)

{-
up' : {Γ₁ Γ₂ : Ctx ∅} → Sub Γ₁ Γ₂ → Sub (⇡ Γ₁) (⇡ Γ₂)
up' (ε Γ) = •⇡ ∘ (ε (⇡ Γ))
up' (id Γ) = id (⇡ Γ)
up' (s , x) = ,⇡ _ _ ∘ (up' s , up x)
up' (s ∘ s') = (up' s) ∘ (up' s')
up' (pr s) = pr (⇡, _ _ ∘ up' s)
up' (down s) = s
-}
\end{code}
}
