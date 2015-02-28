open import Base
open import Nat
open import Id
open import Boolean

module LessThan where

sub : (m : ℕ) → (n : ℕ) → (n ≤ m) → ℕ
sub zero zero (0≤ .0) = 0
sub zero (succ n) ()
sub (succ m) zero (0≤ .(succ m)) = succ m
sub (succ m) (succ n) (succ≤ y) = sub m n y

trich : (m : ℕ) → (n : ℕ) → ((m ≤ n) ⊕ (n ≤ m))
trich zero y = i₁ (0≤ y)
trich (succ x) zero = i₂ (0≤ (succ x))
trich (succ x) (succ y) = recSum (λ a → i₁ (succ≤ a)) (λ b → i₂ (succ≤ b)) (trich x y)

_le_ : ℕ → ℕ → Bool
m le n = recSum (λ a → true) (λ b → false) (trich m n)

_eq_ : ℕ → ℕ → Bool
m eq n = recSum (λ a → (recSum (λ b → true) (λ c → false) (trich n m))) (λ b → false) (trich m n)

_lt_ : ℕ → ℕ → Bool
m lt n = recSum (λ a → (if ((sub n m a) eq 0 ) then false else true )) (λ b → false) (trich m n)

_gt_ : ℕ → ℕ → Bool
m gt n = recSum (λ a → false) (λ b → true) (trich m n)

leLemma₁ : {a b : ℕ} → (a ≤ b) → (a ≤ (1 + b))
leLemma₁ (0≤ n) = 0≤ (1 + n)
leLemma₁ (succ≤ m) = succ≤ (leLemma₁ m)

leThm₁ : {a b : ℕ} → (a ≤ b) → (c : ℕ) → (a ≤ (b + c))
leThm₁ (0≤ n) zero = 0≤ (n + zero)
leThm₁ (succ≤ m) zero = succ≤ (leThm₁ m zero)
leThm₁ (0≤ n) (succ c) = 0≤ (n + (succ c))
leThm₁ (succ≤ m) (succ c) = succ≤ (leThm₁ m (succ c))

leThm₂ : {a b c : ℕ} → (a ≤ b) → (a ≤ c) → (a ≤ (b + c))
leThm₂ {c = p} x y = leThm₁ x p

leLemma₂ : {a b : ℕ} → (a ≤ b) → (a ≤ (3 * b))
leLemma₂ pf = leThm₂ (leThm₂ pf pf) pf

leLemma₃ : {a b : ℕ} → (a ≤ b) → (a ≤ (4 * b))
leLemma₃ pf = leThm₂ (leLemma₂ pf) pf

leThm₃ : {a b : ℕ} → (a ≤ b) → (c : ℕ) → (a ≤ ((succ c) * b  ))
leThm₃ (0≤ n) zero = 0≤ (1 * n)
leThm₃ (succ≤ x) zero = succ≤ (leThm₃ x zero)
leThm₃ (0≤ n) (succ y) = 0≤ ((succ (succ y)) * n)
leThm₃ (succ≤ x) (succ y) = leThm₂ (leThm₃ (succ≤ x) y) (succ≤ x)

leTrans : {x y z : ℕ} → (x ≤ y) → (y ≤ z) → (x ≤ z)
leTrans (0≤ 0) (0≤ n) = 0≤ n
leTrans (0≤ ._) (succ≤ y) = {!!}
leTrans (succ≤ x₁) (succ≤ y) = {!!}
