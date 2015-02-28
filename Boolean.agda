module Boolean where

open import Base

data Bool : Type where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_&_ : Bool → Bool → Bool
_&_ true y = y
_&_ false y = false

!_ : Bool → Bool
! true = false
! false = true

_||_ : Bool → Bool → Bool
true || y = true
false || y = y

_xor_ : Bool → Bool →  Bool
x xor y = (x & not y) || (not x & y)

nand₀ : Bool → Bool → Bool
nand₀ x y = (not x) || (not y)

nand₁ : Bool → Bool → Bool
nand₁ true y = not y
nand₁ false y = true

nand₂ : Bool → Bool → Bool
nand₂ = λ x y → (not x) || (not y)

if_then_else : {A : Type} → Bool → A → A → A
if_then_else true x _ = x
if_then_else false _ y = y


