-- struct Node {
--   int x;
--   struct Node* next;
-- }

-- Null for the empty list;

module List.L where
open import Library.Nat
open import Library.Nat.Properties
open import Library.Equality
open import Library.Equality.Reasoning

data List (A : Set) : Set where
  [] : List A                    -- nil
  _::_ : A -> List A -> List A   -- cons

infixr 5 _::_

length : ∀{A : Set} -> List A -> ℕ
length [] = 0
length (_ :: xs) = succ (length xs)

[_] : ∀{A : Set} → A → List A
[_] x = x :: []

_++_ : ∀{A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _++_

length-++ : ∀{A : Set} (xs ys : List A) → length xs + length ys == length (xs ++ ys)
length-++ [] ys = refl
length-++ (x :: xs) ys = cong succ (length-++ xs ys)

++-assoc : ∀{A : Set} (xs ys zs : List A) → xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = cong(_::_ x) (++-assoc xs ys zs)

++-unit-l : ∀{A : Set} (xs : List A) → xs == [] ++ xs
++-unit-l xs = refl

++-unit-r : ∀{A : Set} (xs : List A) → xs == xs ++ []
++-unit-r [] = refl
++-unit-r (x :: xs) = cong (x ::_) (++-unit-r xs)

reverse : ∀{A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-++ : ∀{A : Set} (xs ys : List A) → reverse (xs ++ ys) == reverse ys ++ reverse xs
reverse-++ [] ys = ++-unit-r (reverse ys)
reverse-++ (x :: xs) ys =
  begin
    reverse ((x :: xs) ++ ys) ==⟨ refl ⟩
    reverse (x :: (xs ++ ys)) ==⟨ refl ⟩
    reverse (xs ++ ys) ++ [ x ] ==⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ] ==⟨ symm (++-assoc (reverse ys) (reverse xs) [ x ]) ⟩
    reverse ys ++ (reverse xs ++ [ x ]) ==⟨ refl ⟩
    reverse ys ++ reverse (x :: xs)
  end

reverse-inv : ∀{A : Set} (xs : List A) → reverse (reverse xs) == xs
reverse-inv [] = refl
reverse-inv (x :: xs) =
  begin
    reverse (reverse (x :: xs)) ==⟨ refl ⟩
    reverse (reverse xs ++ [ x ]) ==⟨ reverse-++ (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs) ==⟨ refl ⟩
    [ x ] ++ reverse (reverse xs) ==⟨ cong([ x ] ++_) ( (reverse-inv xs)) ⟩
    [ x ] ++ xs ==⟨ refl ⟩
    x :: xs
  end

-- HOMEWORK: specify and prove the property saying that the length of a list is equal to
-- the length of the list reversed

length-rev : ∀{A : Set} (xs : List A) → length xs == length (reverse xs)
length-rev []         = refl
length-rev (x :: xs)  =
  begin
    length (x :: xs)                    ==⟨ refl ⟩
    succ (length xs)                    ==⟨ cong succ (length-rev xs) ⟩
    succ (length (reverse xs))          ==⟨ refl ⟩
    1 + length (reverse xs)             ==⟨ +-comm 1 (length (reverse xs)) ⟩
    length (reverse xs) + 1             ==⟨ refl ⟩
    length (reverse xs) + length [ x ]  ==⟨ length-++ (reverse xs) [ x ] ⟩
    length (reverse xs ++ [ x ])        ==⟨ refl ⟩
    length (reverse (x :: xs))
  end
