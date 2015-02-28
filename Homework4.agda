open import Base
open import Boolean
open import List
open import Nat

recList : {A X : Type} → X → (A → List A → X → X) → List A → X
recList x₀ f [] = x₀
recList x₀ f (x :: x₁) = f x x₁ (recList x₀ f x₁)

_contains₀_ : {A : Type} → List A → (A → Bool) → Bool
_contains₀_ = recList (λ p → false) (λ x xs r → (λ p →  (p x) || (r p)))

recBool : {X : Type} → X → X → Bool → X
recBool x₁ x₂ true = x₁
recBool x₁ x₂ false = x₂

not₀ : Bool → Bool
not₀ = recBool false true 

and₀ : Bool → Bool → Bool
and₀ = recBool (λ n → n) (λ _ → false) 


map₁ : {A X : Type} → List A → (A → X) → List X
map₁ = recList (λ f → []) (λ a as mas → (λ f → (f a) :: (mas f)))

reverse₁ : {A : Type} → List A → List A
reverse₁ = recList ([]) (λ a as ras → ras ++ (a :: []))

lengthnew : {A : Type} → List A → ℕ
lengthnew = recList (0) (λ a as las → succ (las))

flatMap₁ : {A X : Type} → List A → (A → List X) → List X
flatMap₁ = recList (λ f → []) (λ a as fmas → (λ f → (f a) ++ (fmas f)))


filter₁ : {A : Type} → List A → (A → Bool) → List A 
filter₁ = recList (λ p → []) (λ a as filas → (λ p → if (p a) then (a :: filas p) else (filas p)))
--[] filter _ = [] 
--(x :: xs) filter p = if (p x) then (x :: (xs filter p)) else (xs filter p)


