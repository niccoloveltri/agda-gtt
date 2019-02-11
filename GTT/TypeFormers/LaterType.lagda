\AgdaHide{
\begin{code}
module GTT.TypeFormers.LaterType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import GTT.Structure
open import GTT.TypeFormers.Later
open import GTT.TypeFormers.FunctionType

open PSh
open ►Obj
open ExpObj
open NatTrans
\end{code}
}

\begin{code}
sem-next : (Γ : SemCtx κ) (A : SemTy κ) (t : SemTm Γ A) → SemTm Γ (► A)
►cone (nat-map (sem-next Γ A t) i x) [ j ] = nat-map t j (Mor Γ i j x)
\end{code}

\AgdaHide{
\begin{code}
►com (nat-map (sem-next Γ A t) i x) [ j ] [ k ] =
  begin
    Mor A j k (nat-map t j (Mor Γ i j x))
  ≡⟨ nat-com t j k (Mor Γ i j x)  ⟩
    nat-map t k (Mor Γ j k (Mor Γ i j x))
  ≡⟨ cong (nat-map t k) (sym (MorComp Γ)) ⟩
    nat-map t k (Mor Γ i k x)
  ∎
nat-com (sem-next Γ A t) i j x = ►eq (λ { j → cong (nat-map t j) (MorComp Γ) })
\end{code}
}

\AgdaHide{
\begin{code}
fmap : (Γ : SemCtx κ) (A B : SemTy κ) 
          → (f : SemTm Γ (► (A ⇒ B))) (t : SemTm Γ (► A))
          → SemTm Γ (► B)
►cone (nat-map (fmap Γ A B f t) i x) [ j ] = fun (►cone (nat-map f i x) [ j ]) j (►cone (nat-map t i x) [ j ])
►com (nat-map (fmap Γ A B f' t') i x) [ j ] [ k ] =
  let f = nat-map f' in
  let t = nat-map t' in
  begin
    Mor B j k (fun (►cone (f i x) [ j ]) j (►cone (t i x) [ j ]))
  ≡⟨ funcom (►cone (f i x) [ j ]) j k (►cone (t i x) [ j ]) ⟩ 
    fun (►cone (f i x) [ j ]) k (Mor A j k (►cone (t i x) [ j ]))
  ≡⟨ cong (fun (►cone (f i x) [ j ]) k) (►com (t i x) [ j ] [ k ]) ⟩
    fun (►cone (f i x) [ j ]) k (►cone (t i x) [ k ]) 
  ≡⟨ cong (λ z → fun z k (►cone (t i x) [ k ])) (sym (►com (f i x) [ j ] [ j ])) ⟩ 
    fun (Mor (A ⇒ B) j j (►cone (f i x) [ j ])) k (►cone (t i x) [ k ])
  ≡⟨ cong (λ z → fun z k (►cone (t i x) [ k ])) (►com (f i x) [ j ] [ k ]) ⟩
    fun (►cone (f i x) [ k ]) k (►cone (t i x) [ k ])
  ∎
nat-com (fmap Γ A B f t) i j x =
  ►eq (λ {k → cong₂ (λ a b → fun (►cone a [ k ]) k (►cone b [ k ]))
                    (nat-com f i j x)
                    (nat-com t i j x)})
\end{code}
}
