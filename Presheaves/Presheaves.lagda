\AgdaHide{
\begin{code}
module Presheaves.Presheaves where

open import Prelude
\end{code}
}

%% Recall that the topos of trees consists presheaves on the first ordinal $\omega$.
%% We take a slightly different approach: we use presheaves on Agda's built-in type \AD{Size} instead.
%% Note that sizes indeed form a category, since they are partially ordered.
%% 
%Each field represents a part of the data.

Presheaves are defined as a record \AD{PSh}.  The fields \AFi{Obj} and
\AFi{Mor} represent the actions on objects and morphisms respectively,
while \AFi{MorId} and \AFi{MorComp} are the functor laws. The type \F{Size<} (\F{↑} \Ar{i}) contains sizes smaller or equal than \Ar{i}. In the type
of \AFi{MorId} we use the reflexivity of the order on sizes which implies \Ar{i} : \F{Size<} (\F{↑} \Ar{i}).
In the type of \AFi{MorComp} we use transitivity. \remove{so that \Ar{k} :
\F{Size<} (\F{↑} \Ar{j}) implies \Ar{k} : \F{Size<} (\F{↑} \Ar{i}),
and the coercion of \Ar{j} : \F{Size<} (\F{↑} \Ar{i}) to \Ar{j} :
\F{Size}.}
\begin{code}
record PSh : Set₁ where
  field
    Obj : Size → Set
    Mor : (i : Size) (j : Size< (↑ i)) → Obj i → Obj j
    MorId : {i : Size} {x : Obj i} → Mor i i x ≡ x
    MorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : Obj i}
      → Mor i k x ≡ Mor j k (Mor i j x)
\end{code}
