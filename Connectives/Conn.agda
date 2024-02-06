module Connectives.Connectives where
open import Library.Nat
open import Library.Bool
open import Library.List
open import Library.Equality
-- Logical connectives and constants

-- Logical expressions in agda

-- A → B		implication   A ⇒ B

-- ∀(x: A) → B		universal quantification 
-- ∀{A : Set} → 	...

-- E == F 		equality		

-- Conjuction A ∧ B

-- data ∧ = \and

data _∧_  (A B : Set) : Set where
     _,_ : A → B → A ∧ B

one-two : ℕ  ∧ ℕ
one-two = 1 , 2

zero-true : ℕ ∧ Bool
zero-true = 0 , true

ten-nil : ℕ ∧ List Bool
ten-nil = 10 , []

fst : ∀{A B : Set} → A ∧ B → A
fst (x , _) = x

snd : ∀{A B : Set} → A ∧ B → B
snd (_ , y) = y

∧-comm : ∀{A B : Set} → A ∧ B → B ∧ A
∧-comm (x , y) = y , x

-- ∨ = \or

-- Disjunction A ∨ B

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

d1 : (true == false) ∨ (10 == 10)
d1 = inr refl

d2 : (true == true) ∨ (10 == 10)
d2 = inl refl

∨-comm : ∀{A B : Set} → A ∨ B → B ∨ A
∨-comm (inl x) = inr x
∨-comm (inr x) = inl x

∨-elim : ∀{ A B C : Set} → (A → C) → (B → C) → A ∨ B → C
∨-elim f g (inl x) = f x
∨-elim f g (inr x) = g x

-- EXERCISES

ex1 : ∀{A B C : Set} →  A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
ex1 (x , inl y) = inl (x , y)
ex1 (x , inr y) = inr (x , y)
-- another way to prove
-- ex1 (x , y) = ∨-elim (λ z → inl (x , z)) (λ z → inr (x , z)) y

ex2 : ∀(x : Bool) → (x == true) ∨ (x == false)
ex2 true = inl refl
ex2 false = inr refl

-- Logical Constants ⊤ ⊥
-- ⊤ = \top
-- ⊥ = \bot
-- ⟨⟩ = ⟨ followed by ⟩

data ⊤ : Set where
  ⟨⟩ : ⊤

data ⊥ : Set where

-- ex falso quodlibet

ex-falso : ∀{A : Set} → ⊥ → A
ex-falso ()

ex3 : ∀{A : Set} → ⊥ → A ∧ ⊥
ex3 ()
-- ex3 p = ex-falso p

ex4 : ∀{A : Set} → A ∨ ⊥ → A
ex4 (inl x) = x

ex5 : ∀{A : Set} → ⊥ ∨ A → A
ex5 (inr x) = x

ex6 : ∀{A : Set} → A → A ∨ ⊥
ex6 p = inl p

-- Negation
-- ¬ = \neg

¬_ : Set → Set
¬_ A = A → ⊥

contradiction : ∀{A : Set} → A → ¬ A → ⊥
-- contradiction p = λ z → z p
contradiction x y = y x

-- contrapositive : ∀{A B : Set} → (A → B) → ¬ B → ¬ A
-- contrapositive x y = {!!}
contrapositive : ∀{A B : Set} → (A → B) → (B → ⊥) → A → ⊥
contrapositive x y z = y (x z)

-- HOMEWORK
-- solve exercise 1 and 2 at the end of the lecture on negation

-- To solve ex7 we need another theorem called "double-negation"
double-negation : ∀{A : Set} → A → ¬ ¬ A
double-negation = contradiction

-- ex7 : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
ex7 : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
ex7 = contrapositive double-negation

ex8 : ∀{A : Set} → A → ¬ ¬ A
ex8 x y = y x

ntop : ¬ ⊤ → ⊥
ntop x = x ⟨⟩

-- Which of the following De Morgan’s laws can be proved?
-- ¬ A ∨ ¬ B → ¬ (A ∧ B)
-- ¬ A ∧ ¬ B -> ¬ (A ∨ B)
-- ¬ (A ∨ B) -> ¬ A ∧ ¬ B
-- ¬ (A ∧ B) -> ¬ A ∨ ¬ B

-- dm1 : ¬ A ∨ ¬ B → ¬ (A ∧ B)
-- dm1 = ?

-- dm2 : ∀ {A B : Set} ¬ A ∧ ¬ B -> ¬ (A ∨ B)
-- dm2 = ?

-- dm3 : ∀{A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B 
-- dm3 = ?

-- dm4 : ∀{A B : Set} → ¬ (A ∧ B) → ¬ A ∨ ¬ B
-- dm4 = ?
