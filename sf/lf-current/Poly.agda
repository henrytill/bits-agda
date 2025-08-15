module lf-current.Poly where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

open import lf-current.Basics using (minustwo; negb; even; odd; _&&_)

repeat : {A : Set} → A → Nat → List A
repeat x zero = []
repeat x (suc count) = x ∷ (repeat x count)

test-repeat₁ : repeat 4 2 ≡ (4 ∷ 4 ∷ [])
test-repeat₁ = refl

test-repeat₂ : repeat false 1 ≡ (false ∷ [])
test-repeat₂ = refl

app : {A : Set} → List A → List A → List A
app = _++_

rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

test-rev₁ : rev (1 ∷ 2 ∷ []) ≡ (2 ∷ 1 ∷ [])
test-rev₁ = refl

test-rev₂ : rev (true ∷ []) ≡ (true ∷ [])
test-rev₂ = refl

length : {A : Set} → List A → Nat
length = List.length

test-length : length (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
test-length = refl

app-nil-r : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
app-nil-r [] = refl
app-nil-r (x ∷ xs) rewrite app-nil-r xs = refl

app-assoc : {A : Set} → (xs ys zs : List A) →
            xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
app-assoc [] ys zs = refl
app-assoc (x ∷ xs) ys zs rewrite app-assoc xs ys zs = refl

app-length : {A : Set} → (xs ys : List A) →
             length (xs ++ ys) ≡ length xs + length ys
app-length [] ys = refl
app-length (x ∷ xs) ys rewrite app-length xs ys = refl

rev-app-distr : {A : Set} → (xs ys : List A) →
                rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-app-distr [] ys rewrite app-nil-r (rev ys) = refl
rev-app-distr (x ∷ xs) ys rewrite rev-app-distr xs ys | app-assoc (rev ys) (rev xs) (x ∷ []) = refl

rev-involutive : {A : Set} → (xs : List A) → rev (rev xs) ≡ xs
rev-involutive [] = refl
rev-involutive (x ∷ xs) rewrite rev-app-distr (rev xs) (x ∷ []) | rev-involutive xs = refl

combine : {A B : Set} → List A → List B → List (A × B)
combine = List.zip

split : {A B : Set} → List (A × B) → List A × List B
split = List.unzip

test-split : split ((1 , false) ∷ (2 , false) ∷ []) ≡ (1 ∷ 2 ∷ [] , false ∷ false ∷ [])
test-split = refl

nth-error : {A : Set} → List A → Nat → Maybe A
nth-error [] _ = nothing
nth-error (x ∷ xs) zero = just x
nth-error (x ∷ xs) (suc n) = nth-error xs n

test-nth-error₁ : nth-error (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 0 ≡ just 4
test-nth-error₁ = refl

test-nth-error₂ : nth-error ((1 ∷ []) ∷ (2 ∷ []) ∷ []) 1 ≡ just (2 ∷ [])
test-nth-error₂ = refl

test-nth-error₃ : nth-error (true ∷ []) 2 ≡ nothing
test-nth-error₃ = refl

hd-error : {A : Set} → List A → Maybe A
hd-error [] = nothing
hd-error (x ∷ xs) = just x

test-hd-error₁ : hd-error (1 ∷ 2 ∷ []) ≡ just 1
test-hd-error₁ = refl

test-hd-error₂ : hd-error ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ≡ just (1 ∷ [])
test-hd-error₂ = refl

do-it-3-times : {A : Set} → (A → A) → A → A
do-it-3-times f a = f (f (f a))

test-do-it-3-times₁ : do-it-3-times minustwo 9 ≡ 3
test-do-it-3-times₁ = refl

test-do-it-3-times₂ : do-it-3-times negb true ≡ false
test-do-it-3-times₂ = refl

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) with f x
... | false = filter f xs
... | true = x ∷ filter f xs

test-filter₁ : filter even (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (2 ∷ 4 ∷ [])
test-filter₁ = refl

length-is-1 : {A : Set} → List A → Bool
length-is-1 xs = length xs == 1

test-filter₂ : filter length-is-1
               ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ []) ∷ (5 ∷ 6 ∷ 7 ∷ []) ∷ ([]) ∷ (8 ∷ []) ∷ [] ) ≡ ((3 ∷ []) ∷ (4 ∷ []) ∷ (8 ∷ []) ∷ [])
test-filter₂ = refl

count-odd-members : List Nat → Nat
count-odd-members xs = length (filter odd xs)

test-count-odd-members₁ : count-odd-members (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-count-odd-members₁ = refl

test-count-odd-members₂ : count-odd-members (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-count-odd-members₂ = refl

test-count-odd-members₃ : count-odd-members [] ≡ 0
test-count-odd-members₃ = refl

test-anon-fun : do-it-3-times (λ n → n * n) 2 ≡ 256
test-anon-fun = refl

test-filter₂' : filter (λ xs → length xs == 1)
                ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ []) ∷ (5 ∷ 6 ∷ 7 ∷ []) ∷ ([]) ∷ (8 ∷ []) ∷ [] ) ≡ ((3 ∷ []) ∷ (4 ∷ []) ∷ (8 ∷ []) ∷ [])
test-filter₂' = refl

filter-even-gt-7 : List Nat → List Nat
filter-even-gt-7 = filter (λ x → (even x) && (7 < x))

test-filter-even-gt-7₁ : filter-even-gt-7 (1 ∷ 2 ∷ 6 ∷ 9 ∷ 10 ∷ 3 ∷ 12 ∷ 8 ∷ []) ≡ (10 ∷ 12 ∷ 8 ∷ [])
test-filter-even-gt-7₁ = refl

test-filter-even-gt-7₂ : filter-even-gt-7 (5 ∷ 2 ∷ 6 ∷ 19 ∷ 129 ∷ []) ≡ []
test-filter-even-gt-7₂ = refl

partition : {A : Set} → (A → Bool) → List A → List A × List A
partition f xs = (filter f xs , filter (λ x → negb (f x)) xs)

test-partition₁ : partition odd (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ 3 ∷ 5 ∷ [] , 2 ∷ 4 ∷ [])
test-partition₁ = refl

test-partition₂ : partition (λ x → false) (5 ∷ 9 ∷ 0 ∷ []) ≡ ([] , (5 ∷ 9 ∷ 0 ∷ []))
test-partition₂ = refl

map : {A B : Set} → (A → B) → List A → List B
map = List.map

test-map₁ : map (λ x → 3 + x) (2 ∷ 0 ∷ 2 ∷ []) ≡ (5 ∷ 3 ∷ 5 ∷ [])
test-map₁ = refl

test-map₂ : map odd (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ (false ∷ true ∷ false ∷ true ∷ [])
test-map₂ = refl
