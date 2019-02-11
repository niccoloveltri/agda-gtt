module Prelude where
  open import Size public
  open import Function public hiding (_$_; id; _∘_; const)
  open import Data.Bool public hiding (_≟_; decSetoid)
  open import Data.Nat public hiding (_≟_; suc; _⊔_)
  open import Relation.Binary.PropositionalEquality public hiding (cong-app)
  open ≡-Reasoning public
  
  open import Prelude.Basics public
  open import Prelude.Syntax public
