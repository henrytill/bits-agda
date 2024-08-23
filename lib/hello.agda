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
