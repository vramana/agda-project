module raghavproject  where 

open import Nat
open import Base
open import Id
open import Boolean
open import Logic


-- define a subset as a funtion from a proposition to a type


data powerset ( A : Type) : Type where
     isSubset : ( A →  Bool) →  powerset A


-- basic set theoretic operations

complement :{ A : Type } →  powerset A  → powerset A
complement (isSubset x) = isSubset (λ a → not (x a))

union : { A : Type } → powerset A → powerset A → powerset A
union ( isSubset x) ( isSubset y ) = isSubset ( λ a → x a || y a )

intersection : { A : Type } → powerset A → powerset A → powerset A
intersection (  isSubset x) ( isSubset y ) = isSubset ( λ a → x a & y a )

difference : { A : Type } → powerset A → powerset A → powerset A
difference ( isSubset x) ( isSubset y) = isSubset( λ a → x a & (not( y a)))

belongs :{ A : Type } →   powerset A →  A  → Bool
belongs ( isSubset prop ) a = prop a

nullsetℕ : powerset ℕ
nullsetℕ = isSubset( λ x → false)



-- defined the minimal element of a set using the equivalence of a → b with  '(not a) or b)   


data minimal (f : ℕ → Bool) : Type  where
  minwithpf : Σ ℕ (λ x → (((y : ℕ) →  ((f y) == true) → (f x == true) → ( x ≤ y)))) → minimal f 

hp : { f : ℕ → Bool } → minimal f  → ℕ
hp (minwithpf [ a , x ]) = a

proof1 : {x : ℕ } {y : ℕ } → ((succ x) ≤ (succ y)) → ( x ≤ y)
proof1 (succ≤ a₁) = a₁

minimalzero : ( f : ℕ → Bool) → ( (f 0) == true ) → minimal f
minimalzero f pf = minwithpf [ zero , (λ x x₁ x₂ → 0≤ x) ]

shift : (  ℕ → Bool) → (ℕ → Bool )
shift f = λ x → f (succ x)

unshift : ( ℕ → Bool ) →  ℕ → Bool 
unshift a zero = false
unshift a (succ x) = a x

NonEmpty : ( f : ℕ → Bool ) → Type
NonEmpty f =  Σ ℕ (λ x → (f x) == true) 

WithoutZero : ( f : ℕ → Bool ) → Type
WithoutZero f = ( NonEmpty f ) × (((f 0) == false))

minimallemma1 : (f : ℕ → Bool) → WithoutZero f → ( minimal (shift f )) → minimal f
minimallemma1 f [ x , y ] z = {!!} 

absurd : ( true == false ) → False
absurd = λ ()

mlemma2 : (f : ℕ → Bool) → (WithoutZero f) → (NonEmpty (shift f))
mlemma2 f [ [ zero , () ] , y ] 
mlemma2 f [ [ succ a , x ] , y ] = [ a , x ]

mlemma3 :  {f : ℕ → Bool} → (f 0 == true) → (f 0 == false) → False
mlemma3 pf₁ = λ x → absurd (sym pf₁ Id.&& x)

contrapositive : {A B : Type} → (A → B) → (B → False) → (A → False) 
contrapositive = λ {A} {B} z z₁ z₂ → z₁ (z z₂)

mlemma4 : (f : ℕ → Bool) → ((f 0 == true) → False) → (f 0 == false) 
mlemma4 f = {!!}

mlemma5 : (f : ℕ → Bool) → (f 0 == true) →  ((f 0 == false) → False)
mlemma5 f pf = {!!}

mlemma6 : (f : ℕ → Bool) → (f 0 == true) ⊕ (f 0 == false)
mlemma6 f = {!!}

mlemma7 : (f : ℕ → Bool) → (NonEmpty f) → (minimal f) ⊕ (NonEmpty (shift f))
mlemma7 f [ a , x ] = {!!}  

mlemma8 : (f : ℕ → Bool) → (NonEmpty f) → (minimal f)
mlemma8 f [ zero , x ] = minimalzero f x
mlemma8 f [ succ a , x ] = {!!}  


-- subtraction of elements

differ :(n : ℕ) →(m : ℕ) → ( n ≤  m)  →  ℕ
differ zero zero z = 0
differ (succ n) zero ()
differ 0 n x = n
differ (succ x)(succ y) z = ( differ ( x) ( y) (proof1 z) )


-- less than as a proposition


_lessthan_ : ℕ → ℕ → Bool
0 lessthan n = true
(succ n) lessthan 0 = false
(succ n )lessthan (succ m ) = n lessthan m




_-1 : ( k : ℕ ) → ( 1  ≤ k ) → ℕ 
_-1 zero ()
_-1 (succ k) x = differ 1 (succ k) x

-- using mutual recursion to find modulo 3

mutual

  is0mod3 : ℕ → Bool
  is0mod3 0 = true
  is0mod3 (succ n) = is2mod3 n 

  is1mod3 : ℕ → Bool
  is1mod3 zero =  false
  is1mod3 (succ n) = is0mod3 n

  is2mod3 : ℕ → Bool
  is2mod3 0 = false
  is2mod3 (succ n)= is1mod3 n 
  


-- function for modulo

_modulo_ : ℕ → ℕ → ℕ
0 modulo _  = 0
(succ a) modulo b = if (((succ a) lessthan b) & (b lessthan (succ a) )) then 0 else succ( a modulo b)


-- a+n = succ ( succ) ... n times

succ^  : ℕ → ( ℕ → ℕ )
succ^ 0 = λ x → x
succ^ ( succ n ) = λ x → succ ( succ^ n  x )

n+=succ^n : ( n : ℕ ) → ( a : ℕ ) → ( ( n + a ) == ( succ^ n a ))
n+=succ^n zero a = refl a
n+=succ^n (succ n) a = succ # n+=succ^n n a


-- identities for add and multiply


leftmul : (a : ℕ ) → ( (0 * a)  == 0 )
leftmul zero = refl 0
leftmul (succ a) = refl 0

right*0 : (a : ℕ) → ((a * 0) == 0)
right*0 0 = refl zero
right*0 (succ n) = (λ a → a + 0) # (right*0 n)


leftidentℕ : (a : ℕ) → ( (0 + a) == a)
leftidentℕ a = refl a

rightidentℕ : (a : ℕ) → ( (a + 0) == a )
rightidentℕ zero = refl 0
rightidentℕ (succ a) = succ # ( rightidentℕ a)

-- proving reqd properties for a well order

reflex : ( a : ℕ ) → ( a ≤ a )
reflex zero = 0≤ 0
reflex (succ a) = succ≤ (reflex a)

antisym : {a : ℕ }{b : ℕ} → ( a ≤ b) → ( b ≤ a) → ( a == b )
antisym (0≤ .0) (0≤ .0) = refl zero
antisym (succ≤ x) (succ≤ y) = succ # (antisym x y)

stepconnex : {a b : ℕ } → ( a ≤ b) ⊕ ( b ≤ a ) → (( succ a ) ≤ ( succ b )) ⊕ ((succ b ) ≤ ( succ a ))
stepconnex (ι₁ x) = ι₁ (succ≤ x)
stepconnex (ι₂ x) = ι₂ (succ≤ x)


connex : (a : ℕ ) → ( b : ℕ ) → ((a ≤ b ) ⊕ ( b ≤ a ))
connex zero zero = ι₁ (0≤ 0)
connex zero (succ b) = ι₁ (0≤ (succ b))
connex (succ a) zero = ι₂ (0≤ (succ a))
connex (succ a) (succ b) = stepconnex (connex a b)
 
transitive : { a b c : ℕ } → ( a ≤ b) → ( b ≤ c ) → (a ≤ c)
transitive {zero} {zero} {zero} x x₁ = 0≤ 0
transitive {zero} {zero} {succ c} x x₁ = 0≤ (succ c)
transitive {zero} {succ b} {c} x x₁ = 0≤ c
transitive {succ a} {succ b}{succ c} (succ≤ x) (succ≤ x₁) = succ≤ (transitive x x₁)

-- commutativity of add

comm+ : ( a b : ℕ ) → (( a + b) == (b + a) )
comm+ zero zero = refl 0
comm+ zero (succ b) = sym ( (rightidentℕ ( succ b)) Id.&& (leftidentℕ (succ b )))
comm+ (succ a) zero = rightidentℕ (succ a) Id.&& leftidentℕ(succ a)
comm+ (succ a) (succ b) = ( ( succ  # (comm+  a ( succ b )  )  ) Id.&& (  (succ^ 2 ) # sym (comm+ a b ) )) Id.&& ( succ # (comm+  (succ a) b ))

{-
--Given a and b return the quotient and remainder
_mod%Succ_ : ℕ → ℕ → ℕ × ℕ
zero mod%Succ b = [ zero , zero ]
succ a mod%Succ b = if p₂(a mod%Succ b) equals b then [ (succ(p₁ (a mod%Succ b))) , 0 ] else [ (p₁ (a mod%Succ b)) , (succ(p₂ (a mod%Succ b)))]
-}
