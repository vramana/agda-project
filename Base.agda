module Base where

Type : Set₁
Type = Set

data _×_  (A B : Type) : Type where
  [_,_] : A → B → A × B

p₁ : {A B : Type} → A × B → A
p₁ ([ a , b ]) = a

p₂ : {A B : Type} → A × B → B
p₂ ([ a , b ]) = b



data _⊕_  (A B : Type) : Type where
  i₁ : A → A ⊕ B
  i₂ : B → A ⊕ B

recSum : {A B X : Type} → (A → X) → (B → X) → (A ⊕ B → X)
recSum f g (i₁ a) = f a
recSum f g (i₂ b) = g b

data Σ (A : Type) (B : A → Type) : Type where
  [_,_] : (a : A) → (B a) → Σ A B

proj₁ : {A : Type} → {B : A → Type} → Σ A B → A
proj₁ ([ a , b ]) = a 

proj₂ : {A : Type} → {B : A → Type} → (ab : Σ A B) → (B (proj₁ ab))
proj₂ ([ a , b ]) = b 


-- Equality type

data _==_ {A : Type} : A → A → Type where
  refl : (a : A) → a == a

dual : {A B : Type} → {C : Type} → (A → B) → (B → C) → (A → C)
dual f φ = λ a → φ (f a)
