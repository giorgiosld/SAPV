module Exercise1.Exercise1 where
open import Library.Nat

f1 : ℕ → ℕ
f1 x = x + 1

f2 : ℕ → ℕ
f2 = λ (x : ℕ) → x + 1

f3 : ℕ → ℕ
f3 = λ x → x + 1

f4 : ℕ → ℕ
f4 x = succ(x)

poly1 : ℕ → ℕ
poly1 x = 2 * x ^ 2

poly2 : ℕ → ℕ → ℕ
poly2 x y = 2 * ( x ^ 3 + y ^ 2)

-- g1 λ (x : ℕ → ℕ → ℕ) (y : ℕ → ℕ) → x y -- nwl

-- g2 : λ (x : (ℕ → ℕ) → ℕ) (y : ℕ) → x y  -- nwl

-- g3 : λ (x : ℕ → ℕ → ℕ) (y : ℕ) → x x y -- nwl

-- g4 : λ (x : ℕ → ℕ → ℕ) (y : ℕ) → x (x y) -- nwl

-- g5 : λ (x : ℕ → ℕ → ℕ) (y : ℕ) → x y y -- nwl

--    M : A → B   N : A
--  ----------------------
--       M N : B

-- if the 2 premises are true so the condition behind the line is also true
