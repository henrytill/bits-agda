module Bits.PropLogic where

-- https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/5.propositional.html

-- Implication
id : {A : Set} → A → A
id a = a

-- First projection
K : {A B : Set} → A → B → A
K a _ = a

-- Application
app : {A B : Set} → (A → B) → A → B
app f a = f a

-- Flip
flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

-- Transitivity / composition
comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp f g a = g (f a)

-- S
S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g a = f a (g a)

open import Data.Product renaming (_×_ to _∧_)

-- Projections
proj1 : {A B : Set} → (A ∧ B) → A
proj1 (a , b) = a

-- Diagonal
diag : {A : Set} → A → (A ∧ A)
diag a = a , a

-- Commutativity
∧-comm : {A B : Set} → (A ∧ B) → (B ∧ A)
∧-comm (a , b) = b , a
