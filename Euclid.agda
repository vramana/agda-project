open import Base
open import Nat
open import Id
open import Boolean
open import LessThan

module Euclid where

{-# NON_TERMINATING #-}
rem : ℕ → (n : ℕ) → (1 ≤ n) → ℕ
rem m zero ()
rem m (succ n) (succ≤ p) = recSum (λ a → (if (m eq succ n) then 0 else m)) (λ b → rem (sub m (succ n) b) (succ n) (succ≤ p)) (trich m (succ n))



{-data _div_ : ℕ → ℕ → Type where
   pf : {a : ℕ} → {b : ℕ} → (p : 1 ≤ a) → ((rem b a p) == 0) → a div b

--prop1 : {a b : ℕ} → (a div b) → (rem b a == 0)
--prop1 (pf a c) = refl (rem (c * a)  a)

prop2 : {a b c : ℕ} → (a div b) → (b div c) → (a div c)
prop2 m n =

-}
