module Nat.Nat where
open import Library.Equality
open import Library.Equality.Reasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{- this is a comment -}

three-is-three : 3 == succ (succ (succ zero))
three-is-three = refl

_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ (x + y)

{-(succ (succ zero)) + (succ zero)
  = ((succ)
-}

one-plus-two : 1 + 2 == 3
one-plus-two = refl

_*_ : ℕ → ℕ → ℕ
zero * y = zero
succ x * y = y + (x * y)

two-times-three : 2 * 3 == 6
two-times-three = refl
infixl 6 _+_
infixl 7 _*_

+-assoc : ∀(x y z : ℕ) → x + (y + z) == (x + y) + z
+-assoc zero y z = refl
+-assoc (succ x) y z = cong succ (+-assoc x y z)

+-unit-r : ∀(x : ℕ) → x == x + 0
+-unit-r zero = refl
+-unit-r (succ x) = cong succ (+-unit-r x)

+-unit-l : ∀(x : ℕ) → x == 0 + x
+-unit-l x = refl

-- CONGRUENCE PROPERTY
-- we can prove f A == f B if we prove that A == B by means of the congruence property
-- of equality with respect to function application
+-succ : ∀(x y : ℕ) → succ x + y == x + succ y
+-succ zero y = refl
+-succ (succ x) y = cong succ (+-succ x y)

+-comm : ∀(x y : ℕ) → x + y == y + x
+-comm zero y = +-unit-r y
+-comm (succ x) y = 
  begin
    (succ x) + y ==⟨ refl ⟩
    succ (x + y) ==⟨ cong succ (+-comm x y) ⟩
    succ (y + x) ==⟨ refl ⟩
    (succ y) + x ==⟨ +-succ y x ⟩
    y + (succ x) 
  end

*-dist-r : ∀(x y z : ℕ) → (x + y) * z == x * z + y * z
*-dist-r zero y z = refl
*-dist-r (succ x) y z =
  begin
    ((succ x) + y) * z    ==⟨ refl ⟩
    (succ (x + y)) * z    ==⟨ refl ⟩
    z + ((x + y) * z)     ==⟨ refl ⟩
    _+_ z ((x + y) * z)   ==⟨ refl ⟩
    (_+_ z) ((x + y) * z) ==⟨ cong (_+_ z) (*-dist-r x y z) ⟩
    z + (x * z + y * z)   ==⟨  +-assoc z (x * z) (y * z) ⟩
    (z + x * z) + y * z   ==⟨ refl ⟩
    (succ x) * z + y * z
  end

*-assoc : ∀(x y z : ℕ) -> x * (y * z) == (x * y) * z
*-assoc zero y z = refl
*-assoc (succ x) y z =
  begin
    succ (x) * (y * z) ==⟨ refl ⟩
    succ x * (y * z) ==⟨ {!!} ⟩
    {!!} ==⟨ {!!} ⟩
    (succ (x) * y) * z
  end
