module Sorted.SortedLists where
open import Library.List
open import Library.Nat
open import Library.LessThan
open import Library.Logic

-- PROBLEM: DEFINE A PREDICATE
-- INDICATE WHETHER A LIST IS SORTED

--  ____ ____ ____ ____ _  lb-[]
--       LowerBound x []

--    x ≤ y Lowerbound x xs
--  ____ ____ ____ ____ ____ lb-::
--  LowerBound x (y :: xs)

--  
--  ____ ____  sorted-[]
--  Sorted []

--  LowerBound x xs     Sorted xs
--  ____ ____ ____ ____ ____ ____  sorted-::
--         Sorted ( x :: xs)

data LowerBound (x : ℕ) : List ℕ → Set where
  lb-[] : LowerBound x []
  lb-:: : {y : ℕ} {xs : List ℕ} → x <= y → LowerBound x xs → LowerBound x (y :: xs)

lower-lower-bound : {x y : ℕ} {ys : List ℕ} → x <= y → LowerBound y ys → LowerBound x ys
lower-lower-bound x≤y lb-[]            = lb-[]
lower-lower-bound x≤y (lb-:: y≤z y≤ys) =
  lb-:: (le-trans x≤y y≤z) (lower-lower-bound x≤y y≤ys)

lb235 : LowerBound 2 (3 :: 5 :: [])
lb235 = lb-:: (le-succ (le-succ le-zero)) (lb-:: (le-succ (le-succ le-zero)) lb-[])

data Sorted : List ℕ → Set where
  sorted-[] : Sorted []
  sorted-:: : {x : ℕ} {xs : List ℕ} →
              LowerBound x xs → Sorted xs →
              Sorted (x :: xs)

_ : Sorted (2 :: 3 :: 5 :: [])
_ = sorted-:: lb235 (sorted-:: (lb-:: (le-succ (le-succ (le-succ le-zero))) lb-[])
                      (sorted-:: lb-[] sorted-[]))

insert : ℕ → List ℕ → List ℕ
insert x []        = [ x ]
insert x (y :: ys) with le-total x y
... | inl x≤y = x :: y :: ys                  -- type x \le y (without space) to enter x≤y
... | inr x≤y = y :: insert x ys

insertion-sort : List ℕ → List ℕ
insertion-sort []        = []
insertion-sort (x :: xs) = insert x (insertion-sort xs)

lower-bound-insert : (x y : ℕ) (ys : List ℕ) → y <= x → LowerBound y ys → LowerBound y (insert x ys)
lower-bound-insert x y []       y≤x lb-[] = lb-:: y≤x lb-[]
lower-bound-insert x y (z :: ys) y≤x (lb-:: y≤z y≤ys) with le-total x z
... | inl x≤z = lb-:: y≤x (lb-:: y≤z y≤ys)
... | inr z≤x = lb-:: y≤z (lower-bound-insert x y ys y≤x y≤ys)

insert-sorted : ∀(x : ℕ) (ys : List ℕ)→ Sorted ys → Sorted (insert x ys)
insert-sorted x []                sorted-[] = sorted-:: lb-[] sorted-[]
insert-sorted x (y :: ys) (sorted-:: y≤ys sor) with le-total x y
... | inl x≤y = sorted-:: (lb-:: x≤y (lower-lower-bound x≤y y≤ys))
                (sorted-:: y≤ys sor)
... | inr y≤x = sorted-:: (lower-bound-insert x y ys y≤x y≤ys) (insert-sorted x ys sor)

insertion-sort-sorted : ∀(xs : List ℕ) → Sorted (insertion-sort xs)
insertion-sort-sorted []        = sorted-[]
insertion-sort-sorted (x :: xs) =
  insert-sorted x (insertion-sort xs) (insertion-sort-sorted xs)

