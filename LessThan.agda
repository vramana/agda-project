open import Base
open import Nat
open import Id
open import Boolean
open import Logic

module LessThan where

-- Helper Functions to various numbers of (m ≤ n)

left≤ : {m n : ℕ} → (m ≤ n) → ℕ
left≤ (0≤ n) = zero
left≤ (succ≤ pf) = succ (left≤ pf)

right≤ : {m n : ℕ} → (m ≤ n) → ℕ
right≤ (0≤ n) = n
right≤ (succ≤ pf) = succ (right≤ pf)

zero≤ : {m n : ℕ} → (m ≤ n) → ℕ
zero≤ (0≤ n) = n
zero≤ (succ≤ pf) = zero≤ pf

-- Subtraction operator

sub : (m : ℕ) → (n : ℕ) → (n ≤ m) → ℕ
sub zero zero (0≤ .0) = 0
sub zero (succ n) ()
sub (succ m) zero (0≤ .(succ m)) = succ m
sub (succ m) (succ n) (succ≤ y) = sub m n y

-- Weak cancellation for ℕ

cancel₁ : {a b : ℕ} → (pf : a ≤ b) → ((a + (sub b a pf)) == b)
cancel₁ {b = zero} (0≤ .0) = refl 0
cancel₁ {b = succ b} (0≤ .(succ b)) = refl (succ b)
cancel₁ {b = succ b} (succ≤ pf) = succ # cancel₁ pf

-- A Version of Law of Trichotomy

trich : (m : ℕ) → (n : ℕ) → ((m ≤ n) ⊕ (n ≤ m))
trich zero y = i₁ (0≤ y)
trich (succ x) zero = i₂ (0≤ (succ x))
trich (succ x) (succ y) = recℕ (λ a → i₁ (succ≤ a)) (λ b → i₂ (succ≤ b)) (trich x y)

-- Comparsion Operators on ℕ

_le_ : ℕ → ℕ → Bool
m le n = recℕ (λ a → true) (λ b → false) (trich m n)

_eq_ : ℕ → ℕ → Bool
m eq n = recℕ (λ a → (recℕ (λ b → true) (λ c → false) (trich n m))) (λ b → false) (trich m n)

_lt_ : ℕ → ℕ → Bool
m lt n = recℕ (λ a → (if ((sub n m a) eq 0 ) then false else true )) (λ b → false) (trich m n)

_gt_ : ℕ → ℕ → Bool
m gt n = recℕ (λ a → false) (λ b → true) (trich m n)


-- Lemmas and Theorems on LessThanOrEq


-- Theorem 1 : If a, b, c ∈ ℕ and a ≤ b & a ≤ c, then a ≤ (b + c)

leLemma₁ : {a b : ℕ} → (a ≤ b) → (a ≤ (1 + b))
leLemma₁ (0≤ n) = 0≤ (1 + n)
leLemma₁ (succ≤ m) = succ≤ (leLemma₁ m)

leLemma₂ : {a b : ℕ} → (a ≤ b) → (c : ℕ) → (a ≤ (b + c))
leLemma₂ (0≤ n) zero = 0≤ (n + zero)
leLemma₂ (succ≤ m) zero = succ≤ (leLemma₂ m zero)
leLemma₂ (0≤ n) (succ c) = 0≤ (n + (succ c))
leLemma₂ (succ≤ m) (succ c) = succ≤ (leLemma₂ m (succ c))

leThm₁ : {a b c : ℕ} → (a ≤ b) → (a ≤ c) → (a ≤ (b + c))
leThm₁ {c = p} x y = leLemma₂ x p


-- Theorem 2 : If a, b, c ∈ ℕ and c ≥ 1 & a ≤ b , then a ≤ (c * b)

leLemma₃ : {a b : ℕ} → (a ≤ b) → (a ≤ (3 * b))
leLemma₃ pf = leThm₁ (leThm₁ pf pf) pf

leLemma₄ : {a b : ℕ} → (a ≤ b) → (a ≤ (4 * b))
leLemma₄ pf = leThm₁ (leLemma₃ pf) pf

leThm₂ : {a b : ℕ} → (a ≤ b) → (c : ℕ) → (a ≤ ((succ c) * b  ))
leThm₂ (0≤ n) zero = 0≤ (1 * n)
leThm₂ (succ≤ x) zero = succ≤ (leThm₂ x zero)
leThm₂ (0≤ n) (succ y) = 0≤ ((succ (succ y)) * n)
leThm₂ (succ≤ x) (succ y) = leThm₁ (leThm₂ (succ≤ x) y) (succ≤ x)


-- Transitivity of LessThanOrEq Operator

-- Theorem 3 : If a, b, c ∈ ℕ and a ≤ b & b ≤ c then a ≤ c

--leTrans : {x y z : ℕ} → (x ≤ y) → (y ≤ z) → (x ≤ z)
--leTrans pf₁ pf₂ = {!!}

-- Strong cancellation for ℕ

--cancel₂ : {a b c : ℕ} → (pf₁ : a ≤ b) → (pf₂ : b ≤ c) → (((sub c b pf₂) + (sub b a pf₁)) == (sub c a (leTrans pf₁ pf₂)))
--cancel₂ x y = {!!}


-- Archimedian property on ℕ

--archProp : {a b : ℕ} → (1 ≤ a) → (a ≤ b) → Σ ℕ (λ c → b ≤ (c * a))
--archProp m n = {!!}
