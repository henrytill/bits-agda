module lf-current.Lists where

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality

module NatProdPlayground where

  data NatProd : Set where
    pair : Nat → Nat → NatProd

  fst : NatProd → Nat
  fst (pair x y) = x

  snd : NatProd → Nat
  snd (pair x y) = y

  fst-pair-3-5 : fst (pair 3 5) ≡ 3
  fst-pair-3-5 = refl

  pattern _,_ x y = pair x y
  infixr 4 _,_

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

module NatListPlayground where

  data NatList : Set where
    nil : NatList
    cons : Nat → NatList → NatList

  pattern [] = nil
  pattern _::_ x y = cons x y

  infixr 5 _::_

  repeat : Nat → Nat → NatList
  repeat n zero = []
  repeat n (suc count) = n :: repeat n count

  length : NatList → Nat
  length [] = zero
  length (x :: l) = suc (length l)

  append : NatList → NatList → NatList
  append [] l₂ = l₂
  append (x :: xs) l₂ = x :: append xs l₂

  _++_ : NatList → NatList → NatList
  x ++ y = append x y

  test-app-1 : (1 :: 2 :: 3 :: []) ++ (4 :: 5 :: []) ≡ (1 :: 2 :: 3 :: 4 :: 5 :: [])
  test-app-1 = refl

  test-app-2 : [] ++ (4 :: 5 :: []) ≡ (4 :: 5 :: [])
  test-app-2 = refl

  test-app-3 : (1 :: 2 :: 3 :: []) ++ [] ≡ (1 :: 2 :: 3 :: [])
  test-app-3 = refl

  hd : Nat → NatList → Nat
  hd default [] = default
  hd default (x :: xs) = x

  tl : NatList → NatList
  tl [] = []
  tl (x :: xs) = xs

  test-hd-1 : hd 0 (1 :: 2 :: 3 :: []) ≡ 1
  test-hd-1 = refl

  test-hd-2 : hd 0 [] ≡ 0
  test-hd-2 = refl

  test-tl : tl (1 :: 2 :: 3 :: []) ≡ (2 :: 3 :: [])
  test-tl = refl
