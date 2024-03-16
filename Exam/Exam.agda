-- @author Giorgio Saldana
-- @email giorgio.saldana@studenti.unicam.it
-- @text
-- data Merge {A : Set} : List A -> List A -> List A -> Set where
-- merge-[] : Merge [] [] []
-- merge-l : {x : A} {xs ys zs : List A} -> Merge xs ys zs ->
-- Merge (x :: xs) ys (x :: zs)
-- merge-r : {y : A} {xs ys zs : List A} -> Merge xs ys zs ->
-- Merge xs (y :: ys) (y :: zs)
-- Note that a proof of Merge xs ys zs represents the fact that zs is a list obtained by
-- merging xs and ys.
-- Solve the following exercises.
-- 1. Prove that the list 0 :: 1 :: 2 :: 3 :: 5 :: [] is the merge of 1 :: 3
-- :: 5 :: [] and 0 :: 2 :: [].
-- 2. Prove that Merge xs ys [] implies xs == [] ∧ ys == [].
-- 3. Prove that Merge xs ys [ x ] implies xs == [] ∨ ys == [] using the
-- solution of the previous exercise.
-- 4. Prove that Merge xs ys zs implies Merge ys xs zs.
-- 5. Prove that Merge xs ys zs implies length zs == length xs + length
-- ys.
-- 6. Prove that Merge xs ys zs implies zs # xs ++ ys.

module Exam.Exam where
open import Library.List
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Nat
open import Library.Nat.Properties
open import Library.List.Permutation


data Merge {A : Set} : List A → List A → List A → Set where
  merge-[] : Merge [] [] []
  merge-l : {x : A} {xs ys zs : List A} → Merge xs ys zs → Merge (x :: xs) ys (x :: zs)
  merge-r : {y : A} {xs ys zs : List A} → Merge xs ys zs → Merge xs (y :: ys) (y :: zs)

-- 1. Prove that the list 0 :: 1 :: 2 :: 3 :: 5 :: [] is the merge of 1 :: 3 :: 5 :: [] and 0 :: 2 :: []
ex1 : Merge (1 :: 3 :: 5 :: []) (0 :: 2 :: []) (0 :: 1 :: 2 :: 3 :: 5 :: [])
ex1 = merge-r (merge-l (merge-r (merge-l (merge-l merge-[]))))

-- 2. Prove that Merge xs ys [] implies xs == [] ∧ ys == []
-- dimostra che se xs e ys mergiati è uguale al vuoto allora xs e ys sono vuoti
ex2 : ∀{A : Set} (xs ys : List A) → Merge xs ys [] → xs == [] ∧ ys == []
ex2 [] [] merge-[] = refl , refl

-- 3. Prove that Merge xs ys [ x ] implies xs == [] ∨ ys == [] using the previous exercise
-- dimostra che se xs e ys danno come risultato la singleton list ([ x ]) allora o
-- xs o ys sono uguali alla lista vuota
ex3 : ∀{A : Set} {x : A} (xs ys : List A) → Merge xs ys [ x ] → xs == [] ∨ ys == []
ex3 (_ :: xs) [] (merge-l merge-[]) = inr refl
ex3 [] (_ :: ys) (merge-r merge-[]) = inl refl

-- 4. Prove that Merge xs ys zs implies Merge ys xs zs
-- dimostra che se xs e ys sono mergiati il loro risultato è uguale a mergiare ys e zs
ex4 : ∀{A : Set} (xs ys zs : List A) -> Merge xs ys zs -> Merge ys xs zs
ex4 .[] .[] .[] merge-[] = merge-[]
ex4 (_ :: xs) ys (_ :: zs) (merge-l p) = merge-r (ex4 xs ys zs p)
ex4 xs (_ :: ys) (_ :: zs) (merge-r p) = merge-l (ex4 xs ys zs p)

-- ex5: Prove that Merge xs ys zs implies length zs == length xs + length ys
-- dimostra che mergiare xs ys e zs port a ad avere una lungehzza di zs uguale a xs sommata ys
ex5 : ∀{A : Set} (xs ys zs : List A) -> Merge xs ys zs -> length zs == length xs + length ys
ex5 .[] .[] .[] merge-[] = refl
ex5 .(_ :: _) ys .(_ :: _) (merge-l p) = {!!}
ex5 xs .(_ :: _) .(_ :: _) (merge-r p) = {!!}
-- ex5 [] [] [] merge-[] = refl
-- ex5 (x :: xs) ys (x :: zs) (merge-l p) = cong succ (ex5 xs ys zs p)
-- ex5 xs (y :: ys) (y :: zs) (merge-r p) = cong succ (ex5 ys xs zs p)


-- ex6: Prove that Merge xs ys zs implies zs # xs ++ ys
-- dimostra che mergiare xs ys e zs implica che zs permutato è uguale a xs concatenato a ys
ex6 : ∀{A : Set} (xs ys zs : List A) → Merge xs ys zs → zs # xs ++ ys
ex6 = {!!}



