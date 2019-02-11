\AgdaHide{
\begin{code}
module GTT.Structure.Contexts where

open import Prelude
open import Presheaves public
\end{code}
}

Semantic judgments, similar to their syntactic counterparts, are indexed by
a clock context. We reuse the type \AD{ClockCtx} for the semantic
clock contexts.
The semantic variable contexts are sets if the clock context is empty, and
they are presheaves otherwise.
%% For the semantics, we first give an interpretation of contexts, types, and terms.
%% Since contexts depend on clock contexts, there are two cases to consider.
%% If the clock context is empty, then we interpret the context as a set.
%% Otherwise, there is a single clock, and then we use presheaves.
%% We define \F{SemCtx} by pattern matching.
\begin{code}
SemCtx : ClockCtx → Set₁
SemCtx ∅ = Set
SemCtx κ = PSh
\end{code}
