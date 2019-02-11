\AgdaHide{
\begin{code}
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
\end{code}
}
For semantic guarded recursive types, we introduce a type of semantic codes for functors.
We cannot reutilize the syntactic grammar \F{Code} since the code for the constant functor should depend on \AD{SemTy} rather than \AD{Ty}.
Instead we use the following definition.

\begin{code}
data SemCode : ClockCtx → Set₁ where
    ∁ : ∀ {Δ} → SemTy Δ → SemCode Δ
    I : ∀ {Δ} → SemCode Δ
    _⊞_ _⊠_ : ∀ {Δ} → SemCode Δ → SemCode Δ → SemCode Δ
    ▸ : SemCode κ → SemCode κ
\end{code}
\AgdaHide{
Again we can evaluate polynomials as endofunctors on \F{SemTy} \AB{Δ}.
\begin{code}
sem-eval : ∀ {Δ} → SemCode Δ → SemTy Δ → SemTy Δ
sem-eval (∁ A) X = A
sem-eval I X = X
sem-eval (P ⊞ Q) X = sem-eval P X ⊕ sem-eval Q X
sem-eval (P ⊠ Q) X = sem-eval P X ⊗ sem-eval Q X
sem-eval (▸ P) X = ►(sem-eval P X)
\end{code}
}

\AgdaHide{
\begin{code}
data μset (P : SemCode ∅) : SemCode ∅ → Set where
  ∁s : {X : Set} → X → μset P (∁ X)
  I : μset P P → μset P I
  _⊠_ : {Q R : SemCode ∅} → μset P Q → μset P R → μset P (Q ⊠ R)
  ⊞₁ : {Q R : SemCode ∅} → μset P Q → μset P (Q ⊞ R)
  ⊞₂ : {Q R : SemCode ∅} → μset P R → μset P (Q ⊞ R)
\end{code}
}

In the remainder of this section, we only discuss guarded recursive \AIC{κ}-types. %in the clock context \AIC{κ}.
The interpretation of \IC{μ} in the clock context \IC{∅} is standard and therefore omitted.
Given a semantic code \AB{P}, our goal is to construct the action on objects and morphisms of a presheaf \F{mu-κ} \AB{P}.
%Since both parts are defined with a similar technique, we only explain how to define the object part \F{muObj} \AB{P}.

A first na\"{i}ve attempt would be to define the action on objects
\F{muObj} \AB{P} as the initial algebra of \F{sem-eval} \AB{P}, where
\F{sem-eval} evaluates a code as an endofunctor on \F{SemTy}
\IC{κ}.
This means defining \F{muObj} \Ar{P} as an inductive type with one constructor taking in input \F{sem-eval} \Ar{P} (\F{muObj} \Ar{P}). This idea does not work, since \F{muObj} \AB{P} is a sized type
while \F{sem-eval} \AB{P} expects a semantic \IC{κ}-type.

Another possibility would be to define \F{muObj} \AB{P} by induction on \AB{P}.
However, there is a problem when we arrive at the \IC{I} constructor.
In this case, we would like to make a recursive call to \F{muObj} applied to the original code \AB{P}, which is unavailable at this point.
We solve the issue by introducing an auxiliary inductive type family \F{muObj'}, which depends on two codes instead of one.
The first code is the original one used to define the guarded recursive type and we do induction on the second one.
Then we define \F{muObj} \AB{P} to be \F{muObj'} \AB{P} \AB{P}.

\remove{
, would be using induction on \AB{P}.
However, there is a problem when we arrive at the identity polynomial.
In that case, a recursive call is made, so we need to refer back to original polynomial \AB{P}, which is unavailable at this point.
To solve that, we use a trick: we define a data type \F{muObj'}, which depends on two polynomials instead of one.
The first polynomial is the polynomial used to define the guarded recursive type and we do induction on the second one.
In the end, we define \F{muObj} \AB{P} to be \F{muObj'} \AB{P} \AB{P}.

The data type \F{muObj'} \AB{P} \AB{Q} is defined as an inductive type.
The constructors say how to construct inhabitans depending on whether \AB{Q} is constant, a product, a sum, \etc.
If \AB{Q} is a product or sum, they are pairs or injections respectively.
For the identity, we need to use \AB{P} to make a recursive call.
}

The constructors of \F{muObj'} \AB{P} \AB{Q} follow the structure of
\AB{Q}. If \AB{Q} is a product we have a pairing constructor, if it is
a sum we have the two injections. When \AB{Q} is the code for the
identity functor, we make a recursive call. For the \AIC{▸} case, we have a constructor \AIC{later} taking two arguments with the same types as the two fields of \F{►Obj}. Since \F{LaterLem} depends both on a sized type and a proof that it is antitone, we need to define \F{muObj'} mutually with its own proof of antitonicity \F{muMor'}.
This construction works since \F{Later} and \F{LaterLim}
take in input part of the data of a presheaf and they crucially do not depend on the functor laws.
\remove{
The main difficulty comes
with the \AIC{▸} case. We need \F{mu-κ} (\IC{▸}
\Ar{P}) to be equivalent (as a presheaf) to \F{►} (\F{mu-κ} \Ar{P}), for each semantic code \Ar{P}. To this end, the constructor \IC{later} takes two arguments with the same types as the two fields of \F{►Obj}.
}
\remove{
However, the main difficulty is \AIC{▸}.
This is because the later modality depends on both the object and morphism part of its argument.
For this reason, we need to define \F{muObj'} and \F{muMor'} mutually.
We define them formally as follows.
}
\begin{code}
mutual
  data muObj' (P : SemCode κ) : SemCode κ → Size → Set where
    const : {X : PSh} {i : Size} → Obj X i → muObj' P (∁ X) i
    rec : ∀{i} → muObj' P P i → muObj' P I i
    _,_ : ∀{Q R i} → muObj' P Q i → muObj' P R i → muObj' P (Q ⊠ R) i
    in₁ : ∀{Q R i} → muObj' P Q i → muObj' P (Q ⊞ R) i
    in₂ : ∀{Q R i} → muObj' P R i → muObj' P (Q ⊞ R) i
    later : ∀{Q i} (x : Later (muObj' P Q) i)
      → LaterLim (muObj' P Q) (muMor' P Q) i x → muObj' P (▸ Q) i
\end{code}

\begin{code}
  muMor' : (P Q : SemCode κ) (i : Size) (j : Size< (↑ i)) → muObj' P Q i → muObj' P Q j
  muMor' P (∁ X) i j (const x) = const (Mor X i j x)
  muMor' P I i j (rec x) = rec (muMor' P P i j x)
  muMor' P (Q ⊠ R) i j (x , y) = muMor' P Q i j x , muMor' P R i j y
  muMor' P (Q ⊞ R) i j (in₁ x) = in₁ (muMor' P Q i j x)
  muMor' P (Q ⊞ R) i j (in₂ x) = in₂ (muMor' P R i j x)
  muMor' P (▸ Q) i j (later x p) = later x (λ { [ k ] → p [ k ] })
\end{code}

\remove{
We define the object part and the morphism part mutually.
Usually, the morphism part depends on the object part, but not the other way around.
Since \F{►} \AB{A} is defined as a limit, it depends on both the object and the morphism part of \AB{A}.
Hence, to define the action of \AIC{►P} on the objecs, both parts are needed, and thus \F{μObj'} and \F{μMor'} are defined mutually.

\To define the elements of \AIC{μ} \AB{P}, we use an intermediate step.
We define a type family \AD{μObj'}, which does not just depend on \AB{P}, but also on a second polynomial \AB{Q}.
In the end, we take the object part of \AIC{μ} \AB{P} to be \AD{μobj} \AB{P} \AB{P} and similar for the morphisms.
This allows us to do induction on \AB{Q} while remembering \AB{P}.

For the product, sum, and constant polynomial, it is straightforward to define the elements.
For later, we use \F{LaterLim} as defined before.
The identity case, on the other hand, requires more thinking.
The input then is something from the presheaf \AIC{μ} \AB{P} of which the object map is \AD{μobj} \AB{P} \AB{P}.
If we were using induction and we arrived at the identity polynomial, we are unable to get the original polynomial.
For that reason, we must keep track of the original polynomial, which is the argument \Ar{P}.
The morphism part \AD{μMor'} also depends on two polynomials and it is defined by induction.
}

\AgdaHide{
\begin{code}
μMor'Id : (P Q : SemCode κ) {i : Size} {x : muObj' P Q i} → muMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {const x} = cong const (MorId X)
μMor'Id P I {i}{rec x} = cong rec (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x , y} = cong₂ _,_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{in₁ x} = cong in₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{in₂ x} = cong in₂ (μMor'Id P R)
μMor'Id P (▸ Q) {i}{later x p} = cong₂-dep later refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : SemCode κ) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : muObj' P Q i}
  → muMor' P Q i k x ≡ muMor' P Q j k (muMor' P Q i j x)
μMor'Comp P (∁ X) {x = const x} = cong const (MorComp X)
μMor'Comp P I {x = rec x} = cong rec (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x , y} = cong₂ _,_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = in₁ x} = cong in₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = in₂ x} = cong in₂ (μMor'Comp P R)
μMor'Comp P (▸ Q) {x = later x p} = cong₂-dep later refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}
}

We define \AD{muMor} \Ar{P} to be \AD{muMor'} \Ar{P} \Ar{P}. 
Since \AD{muMor} preserves the identity and composition, we get a presheaf \AD{mu-κ} \Ar{P} for each \Ar{P}.
This is used to interpret \IC{μ} in the clock context \IC{κ}. We write \F{mu} for the interpretation of \IC{μ} in a general clock context.
\AgdaHide{
\begin{code}
μ-κ : SemCode κ → SemCode κ → SemTy κ
μ-κ P Q = record
  { Obj = muObj' P Q
  ; Mor = muMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }
\end{code}
}
\remove{
The presheaf \AD{μ-κ} \AB{P} \AB{P} gives the interpretation for \AIC{μ} in the clock context \AIC{κ}.
}
\AgdaHide{
\begin{code}
mu : ∀ {Δ} → (P : SemCode Δ) → SemTy Δ
mu {κ} P = μ-κ P P
\end{code}
}

\AgdaHide{
\begin{code}
mu {∅} P = μset P P
\end{code}
}
