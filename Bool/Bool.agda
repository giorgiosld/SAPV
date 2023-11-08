module Bool.Bool where
open import Library.Equality

data Bool : Set where
  true : Bool
  false : Bool

-- this style of definine functions is called "DEFINITION BY CASE ANALYSIS"
-- in this case agda use the pattern matching
-- if arg is true, argument match to pattern false
-- if arg is false, argument match to pattern true
-- not : Bool → Bool
-- not true = false
-- not false = true

-- another way to define functions
not : Bool → Bool
-- ? stands of idk what write here. it means i'll fill but now idk what is
-- not x = ? -> not x = { }0
-- we can do ctrl c + d or ctrl + n and agda can help us to find what write
-- we can ask also at agda to complete using ctr +c ctrl +c. At this point
-- agda ask us the name of variable in which we want perform CASE ANALYSIS
-- in this case x
-- doing so we obtain not true = {}0 \n not false = {}1
-- we can solve the equation then press ctrl+space
not true = false
not false = true
-- if we type ctrl c +ctrl, we can obtain the goal (list og things that can useful)
-- to fill our question

and : Bool → Bool → Bool
-- we can use everytime ctrl c+ctrl c to help us with case analysis
-- and x y = {}0
-- we can use again ctrl c+ctrl c with x as parm
-- we obtain and true y = {}0 \n and false y = {}1
-- we write again ctrl c+ctrl c with parm y and obtain
-- and true true = {}0
-- and true false = {}1
-- and false y = {}2
-- we can performa again case analysis with parm y and obtain finally
-- and true true = {}0
-- and true false = {}1
-- adn false true = {}2
-- and false false = {}3
-- fill the brackets and obtain the correct pattern matching
-- and true true = true
-- and true false = false
-- and false true = false
-- and false false = false
and true y = y
and false y = false

-- _ to the left to the right is added because _ within an identifier have a special
-- meaning, whenever we put we're telling to agda that if we like we can also
-- apply this function to 2 argument instead apply to a parameter
-- this is called INFIX NOTATION
-- true && false
_&&_ : Bool → Bool → Bool
_&&_ true y = y
_&&_ false y = false
-- fixity declaration
-- infixl where l contraction of left
-- infixr where r contraction of right
-- 6 tells the intended priority of this operator
infixl 6 _&&_

-- a is a proof the true is equal to false
-- where are not able to fill the hole that tells true is equals to false
-- for the equivalence reationship is necessary have 3 properties:
-- 1- reflexivity
-- 2- simmetry
-- 3- tranisitivity
true-eq : true == true
true-eq = refl

false-eq : false == false
false-eq = refl

not-true-eq : not true == false
-- not-true-eq : false == false
not-true-eq = false-eq

-- PROVE THAT not IS AN INVOLUTION

-- ∀(x : Bool). not (not x) == x

not-inv : (x : Bool) → not (not x) == x 
not-inv true = true-eq
not-inv false = false-eq

-- PROPERTY: CONJUNCTION IS COMMUTATIVE
-- ∀(x : Bool).∀(y : Bool). x && y == y && x
&&-comm : ∀(x : Bool) → ∀(y : Bool) → x && y == y && x
-- &&-comm : ∀(x y : Bool) → x && y == y && x 
&&-comm true true = refl
&&-comm true false = refl
&&-comm false true = refl
&&-comm false false = refl
