module Fibonacci.proof where
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Nat
open import Library.Nat.Properties

fibo : ℕ -> ℕ
fibo 0               = 0
fibo 1               = 1
fibo (succ (succ k)) = fibo k + fibo (succ k)

fibo-from : ℕ -> ℕ -> ℕ -> ℕ
fibo-from m n 0               = m
fibo-from m n 1               = n
fibo-from m n (succ (succ k)) = fibo-from n (m + n) (succ k)

fast-fibo : ℕ -> ℕ
fast-fibo = fibo-from 0 1

lemma : ∀(k i : ℕ) -> fibo-from (fibo k) (fibo (succ k)) i == fibo (i + k)
lemma k 0 = refl
lemma k 1 = refl
lemma k (succ (succ i)) =
  begin
    fibo-from (fibo (succ k)) (fibo k + fibo (succ k)) (succ i) ==⟨⟩
    fibo-from (fibo (succ k)) (fibo (succ (succ k))) (succ i)
      ==⟨ lemma (succ k) (succ i) ⟩
    fibo (succ i + succ k) ==⟨⟩
    fibo (succ (i + succ k))
      ==⟨ cong (λ x -> fibo (succ x)) (+-comm i (succ k)) ⟩
    fibo (succ (succ k + i)) ==⟨⟩
    fibo (succ (succ (k + i)))
      ==⟨ cong (λ x -> fibo (succ (succ x))) (+-comm k i) ⟩
    fibo (succ (succ (i + k)))
  end

theorem : ∀(k : ℕ) -> fast-fibo k == fibo k
theorem k =
  begin
    fast-fibo k     ==⟨⟩
    fibo-from 0 1 k ==⟨ lemma 0 k ⟩
    fibo (k + 0)    ==⟨ cong fibo (+-unit-r k) ⟩
    fibo k
  end
