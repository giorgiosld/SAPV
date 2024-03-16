module Simulation.Exam2 where
open import Library.Nat
open import Library.List
open import Library.LessThan
open import Library.Logic
open import Library.Equality
-- to use ex-falso
open import Library.Logic.Laws
-- to use #
open import Library.List.Permutation

-- ∈ \in
data _∈_ {A : Set} (x : A) : List A → Set where
  in-head : {xs : List A} → x ∈ (x :: xs)
  in-tail : {y : A} {xs : List A} → x ∈ xs → x ∈ (y :: xs)

infix 4 _∈_
-- Prove that a number (2) belongs to given list
ex1 : 2 ∈ (0 :: 1 :: 2 :: 3 :: 4 :: [])
ex1 = in-tail (in-tail in-head)

-- Prove that x belongs to any list of the form xs ++ x :: ys
ex2 : ∀{A : Set} (x : A) (xs ys : List A) → x ∈ xs ++ x :: ys
ex2 x []         ys = in-head
ex2 x (x₁ :: xs) ys = in-tail (ex2 x xs ys)

-- Prove that x ∈ xs implies 1 <= length xs
ex3 : ∀{A : Set} {x : A} {xs : List A} → x ∈ xs → 1 <= length xs
ex3 in-head     = le-succ le-zero
ex3 (in-tail x) = le-succ le-zero


-- Prove ∀{A : Set} (xs : List A) → (∀(x : A) → ¬ (x ∈ xs)) → xs == []
ex4 : ∀{A : Set} (xs : List A) → (∀(x : A) → ¬ (x ∈ xs)) → xs == []
ex4 []        p = refl
ex4 (x :: xs) p = ex-falso (p x in-head) 

-- Prove that if x belongs to xs and ys is a permutation of xs, then x belongs to ys
ex5 : ∀{A : Set} {x : A} {xs ys : List A} → xs # ys → x ∈ xs → x ∈ ys
-- when use # always see the definition of permutation major of times the definition is sufficent to proof 
-- alway perform case analysis on x that represent xs # ys
ex5 #refl         p = p
-- if we cannot manage the solution perform another case analysis
ex5 #swap in-head     = in-tail in-head
-- again case analysis on p
ex5 #swap (in-tail in-head)     = in-head
ex5 #swap (in-tail (in-tail p)) = in-tail (in-tail p)
-- again ca
ex5 (#cong x) in-head     = in-head
ex5 (#cong x) (in-tail p) = in-tail (ex5 x p)
ex5 (#trans x x₁) p       = ex5 x₁ (ex5 x p)

-- Prove that x ∈ xs ++ ys implies x ∈ xs ∨ x ∈ ys
ex6 : ∀{A : Set} {x : A} (xs ys : List A) -> x ∈ xs ++ ys -> x ∈ xs ∨ x ∈ ys
-- ex6 []        ys = inr
-- ex6 (x :: []) [] = inl
-- ex6 (x :: x₁ :: []) [] = inl
-- ex6 (x :: x₁ :: x₂ :: []) [] = inl
-- we can perform this to infinite so this isn't the solution and we start approaching using with constructor
-- with is used when we cannot determine which is the result or behaviour of an expression
-- ex6 (x :: x₁ :: x₂ :: x₃ :: xs) [] with ex6 xs ys p = {!!}
-- ex6 (x :: xs) (x₁ :: ys) = {!!}
ex6 []        ys p = inr p
-- here is better perform case analysis on p instead of perform in ys
ex6 (x :: xs) ys in-head     = inl in-head
-- here is better use with construct to split the possible result obtained in the construct
ex6 (x :: xs) ys (in-tail p) with ex6 xs ys p
... | inl x₁ = inl (in-tail x₁)
... | inr x₁ = inr x₁


-- ex6 : ∀{A : Set} {x : A} (xs ys : List A) -> x ∈ xs ++ ys -> x ∈ xs ∨ x ∈ ys
-- ex6 [] ys p = inr p
-- ex6 (x :: xs) ys in-head = inl in-head
-- ex6 (y :: xs) ys (in-tail p) with ex6 xs ys p
-- ... | inl q = inl (in-tail q)
-- ... | inr q = inr 
