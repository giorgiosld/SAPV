module Predicates.Pred where
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning

data Even : ℕ → Set where
  ez : Even zero
  es : ∀{n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  oo : Odd 1
  os : ∀{n : ℕ} → Odd n → Odd (succ (succ n))

six-even : Even 6
six-even = es (es (es ez))

five-odd : Odd 5
five-odd = os (os oo)

-- Ex1: Prove that the successor of an even number is odd
Succ-even-odd : ∀(n : ℕ) → Even n → Odd (succ n)
Succ-even-odd zero             ez    = oo
Succ-even-odd (succ (succ n)) (es p) = os (Succ-even-odd n p)

-- Ex2: Prove that the successor of an odd number is even
Succ-odd-even : ∀(n : ℕ) → Odd n → Even (succ n)
Succ-odd-even 1 oo                   = es ez
Succ-odd-even (succ (succ n)) (os p) = es (Succ-odd-even n p)
-- Succ-odd-even (succ (succ _)) (os p) = es (Succ-odd-even _ p)

-- Exercise: Prove that every natural number is either even or odd
thm1 : ∀(n : ℕ) → Even n ∨ Odd n
thm1 zero     = inl ez
thm1 (succ n) with thm1 n
... | p = {!!}

-- ... | inl x = inr (Succ-even-odd n x)
-- ... | inr x = inl (Succ-odd-even n x)
-- Homework: find another solution to the previous exercise which makes
-- use of the elimination principle of disjuntion v-elim and therefore
-- without performing case analisys on p

-- thm2 : ∀(n : ℕ) → ¬ (Even n ∧ Odd n)
-- thm2 zero      = {!!}
-- thm2 (succ n)  = {!!}
-- when we need to proof negation this is a sintattic sugar for a proof like
-- not p is a short way to write p → ⊥
-- so when the negation appears in the codomain what we really means we have
-- an extra argument and we ave to obtain a proof of bottom
thm2 : ∀(n : ℕ) → (Even n ∧ Odd n) → ⊥
thm2 (succ (succ n)) (es x , os y) = thm2 n (x , y)

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

-- Ex3: Prove that the predecessor of an odd number is even
-- Ex4: Prove that if n is even then n == half n + half n
ex4 : ∀{n : ℕ} → Even n → n == half n + half n
ex4 {zero}             ez    = refl
ex4 {(succ (succ n))} (es p) =
  begin
    succ (succ n)                    ==⟨ cong succ (cong succ (ex4 p)) ⟩
    succ (succ (half n + half n))    ==⟨ refl ⟩
    succ (succ (half n) + half n)    ==⟨ cong succ (+-comm (succ (half n) ) (half n) ) ⟩
    succ (half n + succ (half n))    ==⟨ refl ⟩
    succ (half n) + succ (half n) 
  end

-- Ex5: Prove that if n is odd then n == succ (half n + half n)
ex5 : ∀{n : ℕ} → Odd n → n == succ (half n + half n)
ex5 oo        = refl
ex5 (os p)    = {!!}

