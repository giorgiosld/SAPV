module Predicates.Le where
open import Library.Nat
open import Library.Equality

data _≤_ : ℕ → ℕ → Set where
  le-zero : ∀{x : ℕ} → 0 ≤ x
  le-succ : ∀{x y : ℕ} → x ≤ y → succ x ≤ succ y

infix 4 _≤_

two-smaller-than-four : 2 ≤ 4
two-smaller-than-four = le-succ (le-succ le-zero)

le-refl : ∀(x : ℕ) → x ≤ x
le-refl zero = le-zero
le-refl (succ x) = le-succ (le-refl x)

le-antisymm : ∀{x y : ℕ} → x ≤ y → y ≤ x → x == y
le-antisymm le-zero     le-zero     = refl
le-antisymm (le-succ p) (le-succ q) = cong succ (le-antisymm p q)

-- Homework

le-trans : ∀{x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
le-trans = {!!}

-- Ex1: Prove that x ≤ x + y for every x and y
-- Ex2: Prove that if x + y ≤ x then y == 0
-- Ex3: Prove that ≤ is a total order, namely prove that for every
-- x and y, either x ≤ y or y ≤ x
