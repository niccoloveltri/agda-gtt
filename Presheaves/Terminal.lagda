\AgdaHide{
\begin{code}
module Presheaves.Terminal where

open import Data.Unit
open import Presheaves.Const 
open import Presheaves.Presheaves
\end{code}
}

One particular constant presheaf of interest, is the terminal presheaf.
On each size, it gives the unit type \AB{⊤}.

\begin{code}
Terminal = Const ⊤
\end{code}
