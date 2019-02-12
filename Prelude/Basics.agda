
module Prelude.Basics where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Size

-- Function extensionality
postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x) → f ≡ g

-- Uniqueness of identity proofs
uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {A} {x} {y} {refl} {refl} = refl

-- Some lemmata about equality
-- -- Dependent functions preserve equality
cong-dep : {A : Set}{P : A → Set}
  → (f : (a : A) → P a)
  → {x y : A} 
  → (e : x ≡ y) → subst P e (f x) ≡ f y
cong-dep f refl = refl

-- -- Functions with two arguments preserve equality
cong₂-dep : {A B : Set}{P : A → Set}
  → (f : (a : A) (p : P a) → B)
  → {a a' : A} {p : P a} {p' : P a'}
  → (e : a ≡ a') → subst P e p ≡ p' → f a p ≡ f a' p'
cong₂-dep f refl refl = refl

-- -- Transport of transitivity
subst-trans : {A : Set}{P : A → Set}
  → {x y z : A}(e : x ≡ y)(e' : y ≡ z)
  → {p : P x}
  → subst P e' (subst P e p) ≡ subst P (trans e e') p
subst-trans refl refl = refl
