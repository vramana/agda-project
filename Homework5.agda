open import Vector
open import Base
open import Nat

_vmap_ : {n : ℕ} → {A B : Type} → Vec A n → (A → B) → Vec B n
[] vmap f = []
(x :: x₁) vmap f = (f x) :: (x₁ vmap f)
