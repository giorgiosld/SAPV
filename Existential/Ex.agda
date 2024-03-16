module Existential.Ex where
open import Library.Nat
open import Library.Nat.Properties
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Logic
open import Library.LessThan

-- ∀(x : A) → B x

-- A ∧ B 		-- non-dependent pair

-- ∃[ x ] (Even x)      -- dependent pair

-- enter Σ to type sigma

--enter \ex to type ∃

-- data ∃ (A : Set) (B : A → Set) : Set where
--  _,_ : ∀(x : A)→ B x → ∃ A B

data Even : ℕ → Set where
  ez : Even 0
  es : {n : ℕ} → Even n → Even (succ (succ n))

ex1 : ∃[ x ] Even x
ex1 = 0 , ez

ex2 : ∃[ x ] Even x
ex2 = 10 , es (es (es (es (es ez))))

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

-- Ex3: Prove that the predecessor of an odd number is even
-- Ex4: Prove that if n is even then n == half n + half n
lemm : ∀{n : ℕ} → Even n → n == half n + half n
lemm {zero}             ez    = refl
lemm {(succ (succ n))} (es p) =
  begin
    succ (succ n)                    ==⟨ cong succ (cong succ (lemm p)) ⟩
    succ (succ (half n + half n))    ==⟨ refl ⟩
    succ (succ (half n) + half n)    ==⟨ cong succ (+-comm (succ (half n) ) (half n) ) ⟩
    succ (half n + succ (half n))    ==⟨ refl ⟩
    succ (half n) + succ (half n) 
  end

ex3 : ∀{n : ℕ} → Even n → ∃[ x ] n == x + x
ex3 {n} p = half n , lemm p

ex4 : ∀(x : ℕ) → ∃[ y ] x <= y 
ex4 x = x , le-refl

ex5 : ∀{x y : ℕ} → x <= y → ∃[ z ] y == x + z
ex5 {zero}   {y}      le-zero     = y , refl
ex5 {succ x} {succ y}(le-succ le) with ex5 le
... | z , eq = z , cong succ eq
-- (y+1) - (x+1) == y-x
-- we have to find z such that succ y == succ x + z


