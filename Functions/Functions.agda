module Functions.Functions where
open import Library.Nat

f : ℕ  →  ℕ
-- f = λ (x : ℕ) → x ^ 2 + 1

-- is equivalent because agda infer the type
-- f = λ x → x ^ 2 + 1

-- this is the preferred one because is very compact way to write the function
-- another way to avoid redundancy of name we can write the function as:
f x = x ^ 2 + 1

-- function with more argument
g : ℕ → ℕ → ℕ
-- g = λ x → λ y → x + y + 1

-- g x = λ y → x + y + 1

-- best way to write a multi-parameters function
g x y = x + y + 1

h : ℕ → ℕ
h x = x + 1 

id : ℕ → ℕ
id x = x


twice : (ℕ → ℕ) → ℕ → ℕ
-- twice f x = f (f x)

twice f = λ x → f (f x)

-- g 43 = λ y → 43 + y + 1

-- function from ℕ to ℕ
-- ℕ → ℕ = (ℕ → ℕ)

-- if the arrow type is "right associative", then
-- Agda is "right associative"
-- ℕ → ℕ → ℕ = ℕ → (ℕ → ℕ)

-- if the arrow type is "left associative", then
-- ℕ → ℕ → ℕ = (ℕ → ℕ) → ℕ


-- λ(arg : A) → M
-- similar
-- λ(arg : ℕ) → arg + 1

-- λ is like an anonymous function in Java or a Lambda exp.
-- arg is the name of the argument of the function
-- A is the type of the argument of the funcyion
-- M is the body of the function

-- in agda we must add a space for squared
-- x^2 not work
-- x ^ 2

-- check if the c
