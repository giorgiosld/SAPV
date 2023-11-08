module Polymorphism.Poly where
open import Library.Bool
open import Library.Nat

idBool : Bool → Bool
idBool x = x

idNat : ℕ → ℕ
idNat x = x

idX : (ℕ → Bool) → (ℕ → Bool)
idX x = x

-- id : ∀(A : Set) → A → A
-- id _ x = x In this case _ is used to say the first argument of ID is not
-- needed 
-- id A x = x

-- to improve the polymorphism we can rewrite the firm of id so now we can
-- skip the writing of Type given by A : Set
id : ∀{A : Set} → A → A
-- id  x = x

-- if we want improve the implicit we can write
id {A} x = x

tr : Bool
-- tr = id true in this particular case after rewrite id agda is able to infer
-- tr = id _ true
-- _ for this agument we don't need to write because agda can understand the
-- type of argument and so infer the type inside our code
-- for improve also here the implicit we can:
tr = id {Bool} true

flip : ∀{A B C : Set} → (A → B → C) → B → A → C
flip f y x = f x y  

_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
_∘_ f g x = f (g x) 
