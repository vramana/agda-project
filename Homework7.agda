open import Base 
open import Homotopy
open import Id

module Homework7 where

-- This assignment was jointly worked on Ramana and Raghav

symmt : {X Y : Type} → {f g : X → Y} → (f ∼ g) → (g ∼ f) 
symmt {X} {_} pf = λ x → (sym (pf x))

_trns_ : {X Y : Type} → {f g h : X → Y} → (f ∼ g) → (g ∼ h) → (f ∼ h)
_trns_ {X} {_}  f∼g g∼h = λ x → (f∼g x) && (g∼h x)

_hash_ : { X Y Z : Type } → { f g : X → Y } → ( f ∼ g )  → ( h : Z → X  )→ (( f ∘ h) ∼ ( g ∘ h ))
pf hash h = λ x → pf (h x)  

_hash2_ :  { X Y Z : Type } → { f g : X → Y } → ( f ∼ g )   → ( h : Y → Z  )→ ( ( h ∘ f) ∼ ( h ∘ g ))
pf hash2 h = λ x → h # pf x

lemma1 : { X Y : Type } → (g : X → Y) → (g ~ (id Y ∘ g ))
lemma1 g = symmt (id∘ g)

lemma2 : { X Y : Type } → {g h : Y → X } → {f : X → Y} →  ((h ∘ f ) ~ id X) → ((id X ∘ g) ~ ((h ∘ f) ∘ g)) 
lemma2 {X} {Y} {g} {h} {f}  pf =  (symmt pf) hash g

--lemma3 : {X Y : Type } → {g h : Y → X } → {f : X → Y} → ((h ∘ f) ∘ g) ~ (h ∘ (f ∘ g))
--lemma3 =   

lemma4 : {X Y : Type } → {g h : Y → X} → {f : X → Y} → ((f ∘ g) ~ id Y) → ((h ∘ (f ∘ g)) ~ (h ∘ id Y))
lemma4 {_} {_} {_} {h} {_} pf = pf hash2 h

prop1 : {X Y : Type} → {g h : Y → X} → {f : X → Y} → ((h ∘ f ) ~ id X) → ((f ∘ g) ~ id Y) → (g ~ h)
prop1 {X} {Y} {g} {h} {f} pf1 pf2 =  (lemma1 g) trns (
                                         (lemma2 {X} {Y} {g} {h} {f} pf1) trns (
                                             (lemma4 {X} {Y} {g} {h} {f} pf2) trns (h ∘id)))   

equiv→quasiEquiv : {X Y : Type } → ( f : X → Y ) → isEquiv f → isQuasiEquiv f
equiv→quasiEquiv f [ h , [ g , [ pf1 , pf2 ] ] ] = [ h , [ (symmt (prop1 pf2 pf1) hash2 f) trns pf1 , pf2 ] ]
