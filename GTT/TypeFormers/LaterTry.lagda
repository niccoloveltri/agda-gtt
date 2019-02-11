\AgdaHide{
\begin{code}
module GTT.TypeFormers.LaterTry where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure

open PSh
\end{code}
}

We now provide a semantic description of the later modality. This is
an operation on types in the \IC{κ} clock context. 
Ideally, we would like to define the object part of the semantic later modality \F{►} as the following limit:
\begin{code}
record ►ObjTry (A : SemTy κ) (i : Size) : Set where
  field
    ►cone : (j : Size< i) → Obj A j
    ►com : (j : Size< i) (k : Size< (↑ j)) → Mor A j k (►cone j) ≡ ►cone k
\end{code}

Notice that the usual recursive definition of the later modality in
the topos of trees \cite{BMSS-synthetic} is equivalent to
$(\blacktriangleright A) (n) = \lim_{k < n} A (k)$. Therefore, \F{
►ObjTry} is an adaptation of this construction to our
setting. Nevertheless, with this definition, we are unable to
implement a terminating semantic fixpoint combinator.

\begin{code}
sem-dfix₁-try : (A : SemTy κ) (i : Size) → ExpObj (► A) A i → ►ObjTry A i
sem-dfix₁-try = ?
\end{code}

To solve this problem, we need a mechanism to suspend computations.
For that, we define
%% Intuitively, an element of type \F{►} \AB{A} is an element of \AB{A}
%% available one time step ahead from now.  For this reason, the main
%% ingredient of defining the later modality is blocking computations.
%% This is done in several steps and first we define a type \AD{SizeLt}

\begin{code}
data SizeLt (i : Size) : Set where
  [_] : (j : Size< i) → SizeLt i
\end{code}

Functions defined by lambda abstraction can always be unfolded via $\beta$-elimination if they have an input.
However, functions defined by pattern matching only are unfolded if they input has the right shape.
The type \AD{SizeLt} allows definitions via pattern matching.
Such definitions can only be unfolded after inspecting the element, which suspends the computation.
This is essential for defining guarded recursion.

From an inhabitant of \AD{SizeLt}, we can obtain an actual size.
Note that this size is only available when we know it is of the shape \IC{[} \AB{j} \IC{]}.

\begin{code}
size : ∀ {i} → SizeLt i → Size
size [ j ] = j
\end{code}

The type \AD{►Obj} \AB{A} is defined similarly to \AD{►ObjTry} \AB{A}, and again we use a record for the definition.
The first field is represented by the type \F{Later}.
On each coordinate \AB{i}, we take the limit of \AB{A} restricted to the sizes smaller than \AB{i}.

\begin{code}
Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)
\end{code}

The second field is more difficult.
Usually, it would be a universally quantified equality, but since the computations are blocked, the equalities must be blocked as well.
To do so, we need an intermediate definition.

\begin{code}
elimLt : {A : Size → Set₁} {i : Size} → ((j : Size< i) → A j)
  → (j : SizeLt i) → A (size j)
elimLt f [ j ] = f j
\end{code}

This function does pattern matching on \F{SizeLt} and we use it to build predicates on \AD{SizeLt}.
Note that the compuation of such predicates are blocked, which allows us to define the type of the second component as follows.
\begin{code}
LaterLim : (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)
  → (i : Size) (x : Later A i) → Set
LaterLim A m i x = (j : SizeLt i)
  → elimLt (λ { j' → (k : SizeLt (↑ j'))
    → elimLt (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) k }) j
\end{code}

\AgdaHide{
\begin{code}
module _ (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)  where

  LaterLimMor : (i : Size) (j : Size< (↑ i)) (x : Later A i)
    → LaterLim A m i x → LaterLim A m j x
  LaterLimMor i j x p [ k ] [ l ] = p [ k ] [ l ]
\end{code}
}

Now we put it all together and we obtain the following definition of the object part.
We can also define an action on the morphisms and show this preserves identity and composition.
All in all, we get

\begin{code}
record ►Obj (A : SemTy κ) (i : Size) : Set where
  field
    ►cone : Later (Obj A) i
    ►com : LaterLim (Obj A) (Mor A) i ►cone
\end{code}

\AgdaHide{
\begin{code}
open ►Obj

►eq' : {A : SemTy κ} {i : Size} {s t : ►Obj A i} → ►cone s ≡ ►cone t → s ≡ t
►eq' {_} {s} {t} refl = cong (λ z → record { ►cone = ►cone t ; ►com = z})
                             (funext (λ {[ j ] → funext (λ {[ k ] → uip})}))

►eq : {A : SemTy κ} {i : Size} {s t : ►Obj A i} → ((j : Size< i) → ►cone s [ j ] ≡ ►cone t [ j ]) → s ≡ t
►eq p = ►eq' (funext (λ {[ j ] → p j}))
\end{code}
}

\AgdaHide{
\begin{code}
module _ (A : SemTy κ) where
\end{code}
}

\AgdaHide{
\begin{code}
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
\end{code}
}

\begin{code}
► : SemTy κ → SemTy κ
\end{code}

\AgdaHide{
\begin{code}
► A = record
    { Obj = ►Obj A
    ; Mor = ►Mor A
    ; MorId = ►MorId A
    ; MorComp = ►MorComp A
    }
\end{code}
}
