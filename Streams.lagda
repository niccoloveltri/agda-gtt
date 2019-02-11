\AgdaHide{
\begin{code}
module Streams where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Prelude
open import Prelude.Syntax
\end{code}
}

\subsection{Example: Streams}
We give a taste of how to program with streams in \GTT.
%First, we define a function \F{decons} which destructs an element of an inductive type.
\AgdaHide{
\begin{code}
decons : ∀ {Δ} {Γ : Ctx Δ} {P : Poly Δ} → Tm Γ (μ P) → Tm Γ (eval P (μ P))
decons {Γ = Γ} {P} = _$_ (primrec P (Pmap P (lambda (π₁ (var Γ (μ P ⊠ eval P (μ P))))))) 
\end{code}
}
To define a type of streams, we first define guarded streams over a \IC{∅}-type \Ar{A}.
It is the least fixpoint of the functor with code \IC{∁} (\IC{⇡} \Ar{A}) \IC{⊠} \IC{▻ I}.
\begin{code}
g-Str : Ty ∅ → Ty κ
g-Str A = μ (∁ (⇡ A) ⊠ ▻ I)
\end{code}
\AgdaHide{
The head of a guarded stream \Ar{xs} is computed in three steps. First
we apply \F{cons-inv} to \Ar{xs}, obtaining a \GTT\ pair of type \IC{∁} (\IC{⇡} \Ar{A}) \IC{⊠} \IC{▻P} (\F{g-Str} \Ar{A}). Then we take the first projection of this pair using the constructor \IC{π₁} and we conclude with an application of \IC{down}, which is necessary since \Ar{A} is a \IC{∅}-type.
\begin{code}
g-hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ) (g-Str A) → Tm Γ A
g-hd {Γ}{A} xs = down (π₁ (decons xs))
\end{code}
The tail of a guarded stream is computed in a similar way, using \IC{π₂} instead of \IC{π₁} and without the application of \IC{down} in the last step. Notice that the tail is a \GTT\ term of type \IC{▻} (\F{g-Str} \Ar{A}), meaning that it is available only one time step ahead from now.
\begin{code}
g-tl : {Γ : Ctx κ} {A : Ty ∅} → Tm Γ (g-Str A) → Tm Γ (▻ (g-Str A))
g-tl {Γ}{A} xs = π₂ (decons xs)
\end{code}
}
The usual type of streams over \Ar{A} is then obtained by applying the \IC{□} modality to \F{g-Str} \Ar{A}.
\begin{code}
Str : Ty ∅ → Ty ∅
Str A = □ (g-Str A)
\end{code}

We compute the head and tail of a stream using a function \F{decons}, which destructs an element of an inductive type. The term \F{decons} is the inverse of \IC{cons} and it is derivable using \IC{primrec}.
Note that in both cases we need to use \IC{unbox}, because of the application of the box modality in the definition of \F{Str}.
For the tail, we also use \IC{box} and \IC{force}. The operations \IC{π₁} and \IC{π₂} are the projections associated to the product type former \IC{⊠}.

\begin{code}
hd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ A
hd xs = down (π₁ (decons (unbox xs)))
\end{code}
\begin{code}
tl : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
tl xs = force (box (π₂ (decons (unbox xs))))
\end{code}

In our Agda formalization, we also construct a function returning the constant stream over a given element of \Ar{A} and a function removing the elements at even indices out of a given stream.


\AgdaHide{
Given a \GTT\ term \Ar{a} of type \Ar{A}, we can construct the constant guarded stream over \Ar{a} using the fixpoint combinator.
\begin{code}
g-const : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm (⇡ Γ) (g-Str A)
g-const a = fix (lambda (cons _ [ wk (up a) & var _ _ ]))
\end{code}
\NV{Here we use wk, which we have not introduced. Also, it would be nice to have the first argument of cons implicit. Similarly, the two arguments of varTm should be implicit.}
The constant stream over \Ar{a} is obtained by boxing the guarded stream \F{g-const} \Ar{a}.
\begin{code}
const-str : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ A → Tm Γ (Str A)
const-str a = box (g-const a)
\end{code}
}

\AgdaHide{
\begin{code}
weakenSΓ : {Δ : ClockCtx} {Γ : Ctx Δ} {A B : Ty Δ} → Tm Γ (A ⟶ B) → Sub (Γ , A) (Γ , B)
weakenSΓ {_} {Γ} {A} {B} s = pr (id (Γ , A)) , app s
\end{code}

\begin{code}
pfix-tm : {Γ : Ctx κ} {A B : Ty κ}
  → Tm (Γ , (A ⟶ ▻ B)) (A ⟶ B) → Tm Γ (A ⟶ B)
pfix-tm {Γ}{A}{B} f = fix (lambda (sub f (weakenSΓ (lambda (lambda (sub (var Γ (▻ (A ⟶ B))) (pr (id ((Γ , ▻ (A ⟶ B)) , A))) ⊛ next (var (Γ , ▻ (A ⟶ B)) A)))))))
\end{code}

\begin{code}
oddrec : {Γ : Ctx ∅} {A : Ty ∅} → Tm (⇡ Γ , (⇡ (Str A) ⟶ ▻ (g-Str A))) (⇡ (Str A) ⟶ g-Str A)
oddrec {Γ} {A} =
  let s = ,⇡ _ _ ∘ upA _ (pr (id _))
      f = wk (var _ _)
      xs = var _ _
  in
  lambda (cons _ [ sub (up (hd xs)) s & f $ (sub (up (tl xs)) s) ])
\end{code}

\begin{code}
odd : {Γ : Ctx ∅} {A : Ty ∅} → Tm Γ (Str A) → Tm Γ (Str A)
odd xs = box ((pfix-tm oddrec) $ (up xs))
\end{code}
}
