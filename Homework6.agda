open import Fin
open import Base
open import List
open import Nat
open import Tree

fold : {A B : Type} → {n : ℕ} → (Fin n → A) → (A → B → B) → B → B
fold {A} {B} {0} _ _ b = b
fold {A} {B} {succ n} col _*_ b = (col (fzero)) * (fold (λ k → col (fsucc k)) _*_ b)

leaves : {A : Type} → RootedTree A → List A
leaves (leaf a) = a :: []
leaves (node c) = fold (λ k → leaves (c k)) _++_ [] 

{-# NON_TERMINATING #-}
leaveS : {A : Type} → RootedTree A → List A
leaveS (leaf a) = a :: []
leaveS (node a) = fold a (λ c d → (leaveS c) ++ d ) [] 
