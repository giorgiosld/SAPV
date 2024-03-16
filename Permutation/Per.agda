module Permutation.Per where
open import Library.Nat
open import Library.List
open import Library.List.Permutation
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.LessThan
open import Library.Logic
open import Sorted.SortedLists

-- infix 4 _#_

-- data _#_ {A : Set} : List A → List A → Set where
--  #refl  : {xs : List A } → xs # xs
--  #swap  : {x y : A} {xs : List A} → x :: y :: xs # y :: x :: xs
--  #cong  : {x : A} {xs ys : List A} → xs # ys → x :: xs # x :: ys
--  #trans : {xs ys zs : List A} → xs # ys → ys # zs → xs # zs
  
_ : 1 :: 2 :: 3 :: 4 :: [] # 1 :: 3 :: 2 :: 4 :: []
_ = #cong #swap

-- π enter \pi
-- #symm : {A : Set} {xs ys : List A} → xs # ys → ys # xs
-- #symm #refl         = #refl
-- #symm #swap         = #swap
-- #symm (#cong π)     = #cong (#symm π)
-- #symm (#trans π π₁) = #trans (#symm π₁) (#symm π)

_ : 1 :: 2 :: 3 :: [] # 3 :: 2 :: 1 :: []
_ = #begin
      1 :: 2 :: 3 :: [] #⟨ #swap ⟩
      2 :: 1 :: 3 :: [] #⟨ #cong #swap ⟩
      2 :: 3 :: 1 :: [] #⟨ #swap ⟩
      3 :: 2 :: 1 :: []
    #end

insert-permutation : (x : ℕ) (xs : List ℕ) → insert x xs # x :: xs
insert-permutation x []        = #refl
insert-permutation x (y :: xs) with le-total x y
... | inl x≤y = #refl
... | inr y≤x =
  #begin
    y :: insert x xs #⟨ #cong (insert-permutation x xs) ⟩
    y :: x :: xs     #⟨ #swap ⟩
    x :: y :: xs
   #end

insertion-sort-permutation : (xs : List ℕ) → insertion-sort xs # xs
insertion-sort-permutation []        = #refl
insertion-sort-permutation (x :: xs) =
  #begin
    insertion-sort (x :: xs)     #⟨ #refl ⟩
    insert x (insertion-sort xs) #⟨ insert-permutation x (insertion-sort xs) ⟩
    x :: insertion-sort xs       #⟨ #cong (insertion-sort-permutation xs) ⟩
    x :: xs
   #end
