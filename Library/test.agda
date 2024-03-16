-- Proof technique: case analisys, using induction hypotesis, defining function recursevily
-- Define reasonable simple Predicates
-- Define suitable Data Type
-- Think Predicate using Inference System
-- Read whole text before start because may be some hints to define something
-- Exercises are connected (Define Predicate, Proof Predicate is correct..)
-- Prof wnat cover the major of topics covered during the course
-- The duration depends on kindly of exam and number of students
-- Possibility to have an oral exam in order to clear all doubts of prof
-- Written part will always be mandatory, and oral part depends on prof
-- Not allowed to consult any teach material and any lecture notes
-- We can consult our library to see codes and import modules

module Simulation.Exam where
open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.LessThan
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Logic

take : ∀{A : Set} → ℕ → List A → List A
take   zero     xs        = []
take   (succ n) []        = []
take   (succ n) (x :: xs) = x :: take n xs 

-- is alway a good idea spent some minutes to understand what the function is supposed to do
-- so the function accept a natural number and a list and truncate that list starting from the position
-- defined by natural number

-- first exercise this means that we need import LessThan
ex1 : ∀{A : Set} (n : ℕ) (xs : List A) → length (take n xs) <= length xs
-- perform case analisys on n because if we see the definition we should be able to understand when we define take
-- ex1 n xs = ?
-- I perform ca first on n only then on the structure of the list beacause in the def we are 2 cases, but in first case
-- the structure of list doesn't matter so in the sense suggest the proper way to proceed

ex1 zero     xs        = le-zero
-- then in the second case we cannot make further progress without using ca on xs
ex1 (succ n) []        = le-zero
ex1 (succ n) (x :: xs) = le-succ (ex1 n xs)

data Prefix {A : Set} : List A → List A → Set where
  prefix-[] : ∀{ys : List A} → Prefix [] ys
  prefix-:: : ∀{x : A} {xs ys : List A} → Prefix xs ys → Prefix (x :: xs) (x :: ys)

-- to prove a few example above there is one
_ : Prefix (0 :: 1 :: []) (0 :: 1 :: 2 :: 3 :: 4 :: [])
_ = prefix-:: (prefix-:: prefix-[])
-- is always a good idea make some example to prove that we are defined the Predicate correctly

ex3 : ∀{A : Set} (n : ℕ) (xs : List A) → Prefix (take n xs) xs
ex3 zero     xs         = prefix-[]
ex3 (succ x) []         = prefix-[]
ex3 (succ x) (x₁ :: xs) = prefix-:: (ex3 x xs)

-- to use ∃ we need to import Logic module
-- for every n e xs exist a list ys such that if we concatenate take n xs and ys
-- we obtain the original list
ex4 : ∀{A : Set} (n : ℕ) (xs : List A)  → ∃[ ys ] take n xs ++ ys == xs
-- first things to do is remember that proving an existential means a providing the pair
-- where the first element of the pair is the witness
-- we know when n is 0 take 0 xs will return [] so in order to obatin xs we have to
-- concatenate the [] with xs
ex4 zero     xs        = xs , refl
-- we perform ca again on xs
-- we are saying that we're considering the case in which xs is a []
-- we have to find which list ys allow us to obtain [] when we concatenate ys to []
-- in this case only [] has this property
ex4 (succ n) []        = [] , refl
-- proving an existential means providing a pair
-- now here we come to the most difficult case because here we take n+1 element out of
-- a list of a form x :: xs and we know that in this case take will return x :: xs whetever is returned by the recursive application of take n xs
-- we have to think of what we trying to proof, so the existential we have to find this
-- list ys which intuitively is what remains from the original list xs after we have removed
-- n elements from that. But if the original list starts from some element x and we're trying to remove at least 1 element
-- this means that the application of take will actually return a list that start with this ex
-- so we have to look at what is the list that remains after take as let say hidden all the n elements in front of xs
-- so this is to say in this case we have to apply ex4 recursevely because only in this way we have able to find out
-- the rest of the list this is one of the cases which we apply this function recursevily and then analyze the result using pattern matchin
ex4 (succ n) (x :: xs) with ex4 n xs
-- because analyzing the result means that we will be able to see the witness ys which
-- allow us which once we concatenated the result to take allow us to recreate the original list
-- We're applyed ex4 recurse and now p is a pair because is a proof of an existential
-- ... | p = {!!}
-- so here we have a proof of an equality that take n xs ++ to ys == xs
-- so what we do here is we choose ys as our witnes because if we do that than
-- what we do is to proof this equality using cong
... | ys , eq = ys , cong (x ::_) eq
-- this is one ex which if we look at the code of solution this isn't too much but in order to understand
-- how to write this code you really have to think what are you trying to proof
-- COnvince ourslef the meaning of ys and the observation in this case instead this list ys is what remains from the list xs
-- after you choke off an elements from that list

-- Proving a conjuction means provide a pair wich components are proof of this property
-- give name to only explicit argument
ex5 : ∀{A : Set} {x y : A} {xs ys : List A} → x :: xs == y :: ys → x == y ∧ xs == ys
-- here remember eq is defined as data type and we can perform ca
-- eq is the proof that the pairs is equal
-- ex5 eq = {!!}
-- the only proof must be built using the refl constructor
-- so performing ca will be replaced by refl
ex5 refl = refl , refl
-- ¬ \neg
-- the idea is to remember how we defined conjuction, disjunction and negation
-- proof conj is a pair 1 is a proof of A 2 is a proof of B
-- negation is just sugar for (A ∨ B) → ⊥
-- so proving something is not true means writing a function which accepts a proof of this fact and creates a proof of bottom
-- which we know does not exist (⊥ data type without constructor)
ex6 : ∀{A B : Set} → A ∧ B → ¬ (¬ A ∨ ¬ B)
-- this means that → A ∧ B → (¬ A ∨ ¬ B)[domain] → ⊥ [codomain]
-- this also means that we can write another argument and this argument is a proof of thi property
-- ex6 (pa , pb) = {!!}
-- p is a proof of disjunction
-- our goal is to proof bottom[impossible] but we still have something in the environment
-- p on which we can perform ca[cc]
-- ex6 (pa , pb) p = {!!}
-- Depending on which constructor we are considering in the 2 cases
-- this p is a proof of not A and remember having a proof of not A means that p is a function
-- which allow us to obtain a proof of ⊥ if we apply this fun to proof of A
ex6 (pa , pb) (inl p) = p pa
-- this p i a proof of not B means that p is a function from B → ⊥ and we have proof of
-- B in the context so 
ex6 (pa , pb) (inr p) = p pb

-- for ex6 there is a different way not performed in this solution:
-- elimination principle of disjunction

-- 1. State and prove the property that the length of take n xs is always smaller
-- than (<=) the length of xs.
-- 2. Define a predicate Prefix such that Prefix xs ys holds if the list xs is a prefix
-- of the list ys (that is, ys begins with xs and is possibly followed by something
-- else). Make sure that Prefix can be used on lists of any type.
-- 3. State and prove the property that take n xs is always a prefix of xs.
-- 4. State and prove the property that, for every natural number n and list xs, there
-- exists a list ys such that take n xs ++ ys == xs.
-- 5. Prove that :: (the constructor of lists) is injective, namely that if x :: xs == y
-- :: ys then x == y and xs == ys.
-- 6. Prove the theorem ∀{A B : Set} -> A ∧ B -> ¬ (¬ A ∨ ¬ B).

