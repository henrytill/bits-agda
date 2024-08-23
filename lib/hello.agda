module hello where

-- 1. An introduction to Agda for Haskell programmers

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

-- Natural Numbers

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = suc (x + y)

-- Exercise 1.1
-- Define the function halve that computes the result of dividing the
-- given number by 2 (rounded down).  Test your definition by
-- evaluating it for several concrete inputs.
halve : Nat → Nat
halve zero = zero
halve (suc zero) = zero
halve (suc (suc n)) = suc zero + halve n

-- Exercise 1.2
-- Define the function for multiplication of two natural numbers.
_*_ : Nat → Nat → Nat
zero * y = zero
(suc x) * y = y + (x * y)

-- Exercise 1.3
-- Define the type Bool with constructors true and false, and define
-- the functions negation, conjunction, and disjunction.

-- Booleans

data Bool : Set where
  false true : Bool
{-# BUILTIN BOOL Bool #-}

not : Bool → Bool
not false = true
not true = false

_&&_ : Bool → Bool → Bool
false && false = false
false && true = false
true && false = false
true && true = true

_||_ : Bool → Bool → Bool
false || false = false
false || true = true
true || false = true
true || true = true

id : {A : Set} → A → A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

-- Lists

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_

-- Exercise 1.4

length : {A : Set} → List A → Nat
length [] = 0
length (x :: xs) = 1 + length xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

-- Pairs

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

-- Exercise 1.5 : Maybe

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] zero = nothing
lookup [] (suc n) = nothing
lookup (x :: xs) zero = just x
lookup (x :: xs) (suc n) = lookup xs n

-- 2. Dependent types

-- Vectors

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

zeroes : (n : Nat) → Vec Nat n
zeroes zero = []
zeroes (suc n) = 0 :: zeroes n

prepend : {A : Set} {n : Nat} → A → Vec A n → Vec A (suc n)
prepend a as = a :: as

-- Exercise 2.1
downFrom : (n : Nat) → Vec Nat n
downFrom zero = []
downFrom (suc n) = n :: downFrom n

_++Vec_ : {A : Set} → {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: xs) = x

-- Exercise 2.2
tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail (x :: xs) = xs

-- Exercise 2.3
dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) =  (x * y) + dotProduct xs ys

-- Finite Sets

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} → Fin n → Fin (suc n)

lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

-- Exercise 2.4
putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero a (x :: xs) = a :: xs
putVec (suc i) a (x :: xs) = x :: putVec i a xs

-- Dependent Pairs

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

fstΣ : {A : Set} {B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y

fromΣ : {A B : Set} → (A ×' B) → (A × B)
fromΣ (x , y) = x , y

toΣ : {A B : Set} → (A × B) → (A ×' B)
toΣ (x , y) = x , y

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)

-- Exercise 2.6

[]' : {A : Set} → List' A
[]' = (0 , [])

_::'_ : {A : Set} → A → List' A → List' A
x ::' (n , xs) = (suc n , x :: xs)

toList' : {A : Set} → List A → List' A
toList' [] = []'
toList' (x :: xs) = x ::' (toList' xs)

fromList' : {A : Set} → List' A → List A
fromList' (zero , []) = []
fromList' (suc n , x :: xs) = x :: fromList' (n , xs)

-- Just riffing here...

toVec : {A : Set} → (xs : List' A) → Vec A (fstΣ xs)
toVec = sndΣ

fromVec : {A : Set} {n : Nat} → Vec A n → List' A
fromVec {n = m} xs = m , xs

length' : {A : Set} → List' A → Nat
length' = fstΣ

-- For any type A and for any x of type, the constructor refl provides evidence that x ≡ x.
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

module tests where
  
  4+5-is-9 : 4 + 5 ≡ 9
  4+5-is-9 = refl
  
  0+1-is-1 : 0 + 1 ≡ 1
  0+1-is-1 = refl

  halve-0-is-0 : halve 0 ≡ 0
  halve-0-is-0 = refl
  
  halve-1-is-0 : halve 1 ≡ 0
  halve-1-is-0 = refl
  
  halve-2-is-1 : halve 2 ≡ 1
  halve-2-is-1 = refl
  
  halve-3-is-1 : halve 3 ≡ 1
  halve-3-is-1 = refl
  
  halve-4-is-2 : halve 4 ≡ 2
  halve-4-is-2 = refl
  
  halve-8-is-4 : halve 8 ≡ 4
  halve-8-is-4 = refl
  
  halve-9-is-4 : halve 9 ≡ 4
  halve-9-is-4 = refl
  
  halve-23-is-11 : halve 23 ≡ 11
  halve-23-is-11 = refl
  
  halve-24-is-12 : halve 24 ≡ 12
  halve-24-is-12 = refl
  
  9*0-is-0 : 9 * 0 ≡ 0
  9*0-is-0 = refl
  
  9*1-is-9 : 9 * 1 ≡ 9
  9*1-is-9 = refl
  
  9*3-is-27 : 9 * 3 ≡ 27
  9*3-is-27 = refl

  _ : (1 :: 2 :: []) ++ (3 :: 4 :: []) ≡ (1 :: 2 :: 3 :: 4 :: [])
  _ = refl

  _ : lookup (1 :: 2 :: 3 :: []) 0 ≡ just 1
  _ = refl

  _ : lookup (1 :: 2 :: 3 :: []) 2 ≡ just 3
  _ = refl

  _ : lookup (1 :: 2 :: 3 :: []) 3 ≡ nothing
  _ = refl

  _ : dotProduct (1 :: 2 :: 3 :: []) (4 :: 5 :: 6 :: []) ≡ 32
  _ = refl

  _ : lookupVec (1 :: 2 :: 3 :: []) (suc (suc zero)) ≡ 3
  _ = refl

  _ : putVec (suc zero) 42 (1 :: 2 :: 3 :: []) ≡ (1 :: 42 :: 3 :: [])
  _ = refl

  p : Bool × Vec Nat 2
  p = true , 1 :: 2 :: []

  _ : fromΣ (toΣ p) ≡ p
  _ = refl

  q : Bool ×' Vec Nat 2
  q = true , 1 :: 2 :: []

  _ : toΣ (fromΣ q) ≡ q
  _ = refl

  r : Σ Nat (Vec Bool)
  r = 2 , true :: false :: []

  s : Σ Nat (Vec Bool)
  s = 0 , []

  trues : (n : Nat) → Vec Bool n
  trues zero = []
  trues (suc n) = true :: trues n

  xs : List Nat
  xs = 1 :: 2 :: 3 :: []

  _ : fromList' (toList' xs) ≡ xs
  _ = refl

  vs : Vec Nat 3
  vs = 1 :: 2 :: 3 :: []

  vs' : List' Nat
  vs' = 3 , vs

  _ : toVec vs' ≡ vs
  _ = refl

  _ : fromVec (toVec vs') ≡ vs'
  _ = refl

  _ : toVec (toList' xs) ≡ vs
  _ = refl
