module Equality.Eq where

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

infix 4 _==_

symm : {A : Set} (x y : A) → x == y → y == x
symm x .x refl = refl

trans : {A : Set} (x y z : A) → x == y → y == z → x == z
-- the above two methods are correct
-- trans x .x z refl q = q
trans x .x .x refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x == y → f x == f y
cong _ refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x == y → P x → P y
subst _ refl q = q        -- P is not necessary and can be replaced by _

-- Homework solve exercise 1 and 5 from keynote




