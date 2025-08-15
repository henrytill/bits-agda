module lf-current.Lists where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Data.Bool using (_∨_; _∧_)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

NatProd : Set
NatProd = Nat × Nat

fst : NatProd → Nat
fst (x , y) = x

snd : NatProd → Nat
snd (x , y) = y

fst-pair-3-5 : fst (3 , 5) ≡ 3
fst-pair-3-5 = refl

fst' : NatProd → Nat
fst' (x , y) = x

snd' : NatProd → Nat
snd' (x , y) = y

swap-pair : NatProd → NatProd
swap-pair (x , y) = (y , x)

surjective-pairing : (p : NatProd) → p ≡ (fst p , snd p)
surjective-pairing (x , y) = refl

snd-fst-is-swap : (p : NatProd) → (snd p , fst p) ≡ swap-pair p
snd-fst-is-swap (x , y) = refl

fst-swap-is-snd : (p : NatProd) → fst (swap-pair p) ≡ snd p
fst-swap-is-snd (x , y) = refl

NatList : Set
NatList = List Nat

repeat : Nat → Nat → NatList
repeat n zero = []
repeat n (suc count) = n ∷ repeat n count

append : NatList → NatList → NatList
append [] l₂ = l₂
append (x ∷ xs) l₂ = x ∷ append xs l₂

test-app-1 : (1 ∷ 2 ∷ 3 ∷ []) ++ (4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
test-app-1 = refl

test-app-2 : [] ++ (4 ∷ 5 ∷ []) ≡ (4 ∷ 5 ∷ [])
test-app-2 = refl

test-app-3 : (1 ∷ 2 ∷ 3 ∷ []) ++ [] ≡ (1 ∷ 2 ∷ 3 ∷ [])
test-app-3 = refl

hd : Nat → NatList → Nat
hd default [] = default
hd default (x ∷ xs) = x

tl : NatList → NatList
tl [] = []
tl (x ∷ xs) = xs

test-hd-1 : hd 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 1
test-hd-1 = refl

test-hd-2 : hd 0 [] ≡ 0
test-hd-2 = refl

test-tl : tl (1 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ [])
test-tl = refl

nonzeros : NatList → NatList
nonzeros [] = []
nonzeros (0 ∷ xs) = nonzeros xs
nonzeros (x ∷ xs) = x ∷ nonzeros xs

test-nonzeros : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
test-nonzeros = refl

isEven : Nat → Bool
isOdd : Nat → Bool

isEven zero = true
isEven (suc n) = isOdd n

isOdd zero = false
isOdd (suc n) = isEven n

oddmembers : NatList → NatList
oddmembers [] = []
oddmembers (x ∷ xs) with isOdd x
... | false = oddmembers xs
... | true = x ∷ oddmembers xs

test-oddmembers : oddmembers (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 3 ∷ [])
test-oddmembers = refl

countoddmembers : NatList → Nat
countoddmembers l = length (oddmembers l)

test-countoddmembers₁ : countoddmembers (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-countoddmembers₁ = refl

test-countoddmembers₂ : countoddmembers (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-countoddmembers₂ = refl

test-countoddmembers₃ : countoddmembers [] ≡ 0
test-countoddmembers₃ = refl

alternate : NatList → NatList → NatList
alternate [] xs₂ = xs₂
alternate xs₁ [] = xs₁
alternate (x₁ ∷ xs₁) (x₂ ∷ xs₂) = x₁ ∷ x₂ ∷ alternate xs₁ xs₂

test-alternate₁ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ [])
test-alternate₁ = refl

test-alternate₂ : alternate (1 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 5 ∷ 6 ∷ [])
test-alternate₂ = refl

test-alternate₃ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 3 ∷ [])
test-alternate₃ = refl

test-alternate₄ : alternate [] (20 ∷ 30 ∷ []) ≡ (20 ∷ 30 ∷ [])
test-alternate₄ = refl

Bag : Set
Bag = NatList

count : Nat → Bag → Nat
count v [] = 0
count v (x ∷ xs) with v == x
... | false = count v xs
... | true = suc (count v xs)

test-count₁ : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 3
test-count₁ = refl

test-count₂ : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 0
test-count₂ = refl

test-sum₁ : count 1 (append (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
test-sum₁ = refl

add : Nat → Bag → Bag
add = _∷_

test-add₁ : count 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
test-add₁ = refl

test-add₂ : count 5 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-add₂ = refl

member : Nat → Bag → Bool
member v [] = false
member v (x ∷ xs) = (x == v) ∨ (member v xs)

test-member₁ : member 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ true
test-member₁ = refl

test-member₂ : member 2 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ false
test-member₂ = refl

remove-one : Nat → Bag → Bag
remove-one v [] = []
remove-one v (x ∷ xs) with x == v
... | false = x ∷ remove-one v xs
... | true = xs

test-remove-one₁ : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-remove-one₁ = refl

test-remove-one₂ : count 5 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-remove-one₂ = refl

test-remove-one₃ : count 4 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
test-remove-one₃ = refl

test-remove-one₄ : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 1
test-remove-one₄ = refl

remove-all : Nat → Bag → Bag
remove-all v [] = []
remove-all v (x ∷ xs) with x == v
... | false = x ∷ remove-all v xs
... | true = remove-all v xs

test-remove-all₁ : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-remove-all₁ = refl

test-remove-all₂ : count 5 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-remove-all₂ = refl

test-remove-all₃ : count 4 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
test-remove-all₃ = refl

test-remove-all₄ : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 0
test-remove-all₄ = refl

included : Bag → Bag → Bool
included [] ys = true
included (x ∷ xs) ys = member x ys ∧ included xs (remove-one x ys)

test-included₁ : included (1 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ true
test-included₁ = refl

test-included₂ : included (1 ∷ 2 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ false
test-included₂ = refl

eqb-refl : (n : Nat) → (n == n) ≡ true
eqb-refl zero = refl
eqb-refl (suc n) rewrite eqb-refl n = refl

add-inc-count : (n : Nat) → (s : Bag) → count n (add n s) ≡ suc (count n s)
add-inc-count n s rewrite eqb-refl n = refl

nil-all : (xs : NatList) → [] ++ xs ≡ xs
nil-all xs = refl

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

tl-length-pred : (xs : NatList) → pred (length xs) ≡ length (tl xs)
tl-length-pred [] = refl
tl-length-pred (x ∷ xs) = refl
