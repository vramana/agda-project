open import Base
open import Nat
open import Id
open import Boolean
open import LessThan

module Euclid where

-- Remainder Function

{-# NON_TERMINATING #-}
rem : ℕ → (n : ℕ) → (1 ≤ n) → ℕ
rem m zero ()
rem m (succ n) (succ≤ p) = recSum (λ a → (if (m eq succ n) then 0 else m)) (λ b → rem (sub m (succ n) b) (succ n) (succ≤ p)) (trich m (succ n))

divisors : ℕ → List ℕ
divisors p = ?

data _div_ : ℕ → ℕ → Type where
  d : (a : ℕ) → (c : ℕ) → (1 ≤ a)  → a div (a * c)

prop1 : {a b : ℕ} → (a div b) → (rem b a == 0)
prop1 m = ?

prop2 : {a b c : ℕ} → (a div b) → (b div c) → (a div c)
prop2 m n = ?

prop3 : {a b c : ℕ} → (a div b) → Σ ℕ (λ c → ((c * a) == b))
prop3 (p a c pf) = ? -- possibly [ c , (λ p → refl (p * a)) c ]

data prime : ℕ → Type where
  pr : (a : ℕ) → ((length (divisors a)) == 2) → prime a

prop4 : {p a b : ℕ} → (prime p) → (p div (a * b)) → ((p div a) ⊕ (p div b))
prop4  = ?

prop5 : {p a b : ℕ} → (p div a) → (p div b) → (p div (a + b))
prop5 = ?

prop6 : {p a b m n : ℕ} → (p div a) → (p div b) → (p div ((m * a) + (n * b)))
prop6 = ?
