module Prelude where
  open import Size public
  open import Function public hiding (_$_; id; _∘_; const)
  open import Data.Bool public hiding (_≟_; decSetoid)
  open import Data.Nat public hiding (_≟_; suc; _⊔_)
  open import Relation.Binary.PropositionalEquality public hiding (cong-app)
  open ≡-Reasoning public

-- Basic definitions (Section 2)
  open import Prelude.Basics public

-- Syntax of GTT and example of streams (Section 3)
  open import Prelude.Syntax public
  open import Prelude.Streams

