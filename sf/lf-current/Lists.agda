module lf-current.Lists where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import lf-current.Basics using (odd; even; _=?_; _<=?_)
open import lf-current.Induct using (add-comm)

ℕ×ℕ : Set
ℕ×ℕ = ℕ × ℕ

fst : ℕ×ℕ → ℕ
fst (x , y) = x

snd : ℕ×ℕ → ℕ
snd (x , y) = y

fst-pair-3-5 : fst (3 , 5) ≡ 3
fst-pair-3-5 = refl

swap-pair : ℕ×ℕ → ℕ×ℕ
swap-pair (x , y) = (y , x)

surjective-pairing : (p : ℕ×ℕ) → p ≡ (fst p , snd p)
surjective-pairing (x , y) = refl

snd-fst-is-swap : (p : ℕ×ℕ) → (snd p , fst p) ≡ swap-pair p
snd-fst-is-swap (x , y) = refl

fst-swap-is-snd : (p : ℕ×ℕ) → fst (swap-pair p) ≡ snd p
fst-swap-is-snd (x , y) = refl

Listℕ : Set
Listℕ = List ℕ

length : Listℕ → ℕ
length = List.length

repeat : ℕ → ℕ → Listℕ
repeat n zero = []
repeat n (suc count) = n ∷ repeat n count

app : Listℕ → Listℕ → Listℕ
app = _++_

test-app₁ : (1 ∷ 2 ∷ 3 ∷ []) ++ (4 ∷ 5 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
test-app₁ = refl

test-app₂ : [] ++ (4 ∷ 5 ∷ []) ≡ (4 ∷ 5 ∷ [])
test-app₂ = refl

test-app₃ : (1 ∷ 2 ∷ 3 ∷ []) ++ [] ≡ (1 ∷ 2 ∷ 3 ∷ [])
test-app₃ = refl

hd : ℕ → Listℕ → ℕ
hd default [] = default
hd default (x ∷ xs) = x

tl : Listℕ → Listℕ
tl [] = []
tl (x ∷ xs) = xs

test-hd₁ : hd 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 1
test-hd₁ = refl

test-hd₂ : hd 0 [] ≡ 0
test-hd₂ = refl

test-tl : tl (1 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ [])
test-tl = refl

nonzeros : Listℕ → Listℕ
nonzeros [] = []
nonzeros (0 ∷ xs) = nonzeros xs
nonzeros (x ∷ xs) = x ∷ nonzeros xs

test-nonzeros : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
test-nonzeros = refl

oddmembers : Listℕ → Listℕ
oddmembers [] = []
oddmembers (x ∷ xs) with odd x
... | false = oddmembers xs
... | true = x ∷ oddmembers xs

test-oddmembers : oddmembers (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 3 ∷ [])
test-oddmembers = refl

countoddmembers : Listℕ → ℕ
countoddmembers l = length (oddmembers l)

test-countoddmembers₁ : countoddmembers (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-countoddmembers₁ = refl

test-countoddmembers₂ : countoddmembers (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-countoddmembers₂ = refl

test-countoddmembers₃ : countoddmembers [] ≡ 0
test-countoddmembers₃ = refl

alternate : Listℕ → Listℕ → Listℕ
alternate [] ys = ys
alternate xs [] = xs
alternate (x ∷ xs) (y ∷ ys) = x ∷ y ∷ alternate xs ys

test-alternate₁ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ [])
test-alternate₁ = refl

test-alternate₂ : alternate (1 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 5 ∷ 6 ∷ [])
test-alternate₂ = refl

test-alternate₃ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 3 ∷ [])
test-alternate₃ = refl

test-alternate₄ : alternate [] (20 ∷ 30 ∷ []) ≡ (20 ∷ 30 ∷ [])
test-alternate₄ = refl

Bag : Set
Bag = Listℕ

count : ℕ → Bag → ℕ
count v [] = 0
count v (x ∷ xs) with v =? x
... | false = count v xs
... | true = suc (count v xs)

test-count₁ : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 3
test-count₁ = refl

test-count₂ : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 0
test-count₂ = refl

test-sum₁ : count 1 (app (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
test-sum₁ = refl

add : ℕ → Bag → Bag
add = _∷_

test-add₁ : count 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
test-add₁ = refl

test-add₂ : count 5 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
test-add₂ = refl

member : ℕ → Bag → Bool
member v [] = false
member v (x ∷ xs) = (x =? v) ∨ (member v xs)

test-member₁ : member 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ true
test-member₁ = refl

test-member₂ : member 2 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ false
test-member₂ = refl

remove-one : ℕ → Bag → Bag
remove-one v [] = []
remove-one v (x ∷ xs) with x =? v
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

remove-all : ℕ → Bag → Bag
remove-all v [] = []
remove-all v (x ∷ xs) with x =? v
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

eqb-refl : (n : ℕ) → (n =? n) ≡ true
eqb-refl zero = refl
eqb-refl (suc n) rewrite eqb-refl n = refl

add-inc-count : (n : ℕ) → (s : Bag) → count n (add n s) ≡ suc (count n s)
add-inc-count n s rewrite eqb-refl n = refl

nil-all : (xs : Listℕ) → [] ++ xs ≡ xs
nil-all xs = refl

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

tl-length-pred : (xs : Listℕ) → pred (length xs) ≡ length (tl xs)
tl-length-pred [] = refl
tl-length-pred (x ∷ xs) = refl

app-assoc : (l₁ l₂ l₃ : Listℕ) → (l₁ ++ l₂) ++ l₃ ≡ l₁ ++ (l₂ ++ l₃)
app-assoc [] l₂ l₃ = refl
app-assoc (_ ∷ t₁) l₂ l₃ rewrite app-assoc t₁ l₂ l₃ = refl

repeat-plus : (c₁ c₂ n : ℕ) → repeat n c₁ ++ repeat n c₂ ≡ repeat n (c₁ + c₂)
repeat-plus zero c₂ n = refl
repeat-plus (suc c₁) c₂ n rewrite repeat-plus c₁ c₂ n = refl

rev : Listℕ → Listℕ
rev [] = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

test-rev₁ : rev (1 ∷ 2 ∷ 3 ∷ []) ≡ (3 ∷ 2 ∷ 1 ∷ [])
test-rev₁ = refl

test-rev₂ : rev [] ≡ []
test-rev₂ = refl

app-length : (xs ys : Listℕ) → length (xs ++ ys) ≡ length xs + length ys
app-length [] ys = refl
app-length (x ∷ xs) ys rewrite app-length xs ys = refl

rev-length : (xs : Listℕ) → length (rev xs) ≡ length xs
rev-length [] = refl
rev-length (x ∷ xs) rewrite
    app-length (rev xs) (x ∷ [])
  | rev-length xs
  | add-comm (length xs) 1
  = refl

app-nil-r : (xs : Listℕ) → xs ++ [] ≡ xs
app-nil-r [] = refl
app-nil-r (x ∷ xs) rewrite app-nil-r xs = refl

rev-app-distr : (xs ys : Listℕ) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-app-distr [] ys rewrite app-nil-r (rev ys) = refl
rev-app-distr (x ∷ xs) ys rewrite rev-app-distr xs ys | app-assoc (rev ys) (rev xs) (x ∷ []) = refl

rev-involutive : (xs : Listℕ) → rev (rev xs) ≡ xs
rev-involutive [] = refl
rev-involutive (x ∷ xs) rewrite rev-app-distr (rev xs) (x ∷ []) | rev-involutive xs = refl

app-assoc₄ : (l₁ l₂ l₃ l₄ : Listℕ) → l₁ ++ (l₂ ++ (l₃ ++ l₄)) ≡ ((l₁ ++ l₂) ++ l₃) ++ l₄
app-assoc₄ l₁ l₂ l₃ l₄ rewrite
    app-assoc (l₁ ++ l₂) l₃ l₄
  | app-assoc l₁ l₂ (l₃ ++ l₄)
  = refl

nonzeros-app : (xs ys : Listℕ) → nonzeros (xs ++ ys) ≡ (nonzeros xs) ++ (nonzeros ys)
nonzeros-app [] ys = refl
nonzeros-app (zero ∷ xs) ys = nonzeros-app xs ys
nonzeros-app (suc x ∷ xs) ys rewrite nonzeros-app xs ys = refl

eqblist : Listℕ → Listℕ → Bool
eqblist [] [] = true
eqblist [] _ = false
eqblist _ [] = false
eqblist (x ∷ xs) (y ∷ ys) with x =? y
... | false = false
... | true = eqblist xs ys

test-eqblist₁ : eqblist [] [] ≡ true
test-eqblist₁ = refl

test-eqblist₂ : eqblist (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 2 ∷ 3 ∷ []) ≡ true
test-eqblist₂ = refl

test-eqblist₃ : eqblist (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 2 ∷ 4 ∷ []) ≡ false
test-eqblist₃ = refl

eqblist-refl : (xs : Listℕ) → eqblist xs xs ≡ true
eqblist-refl [] = refl
eqblist-refl (x ∷ xs) rewrite eqb-refl x | eqblist-refl xs = refl

count-member-nonzero : (s : Bag) → (1 <=? (count 1 (1 ∷ s))) ≡ true
count-member-nonzero [] = refl
count-member-nonzero (x ∷ s) = refl

leb-n-suc-n : (n : ℕ) → (n <=? (suc n)) ≡ true
leb-n-suc-n zero = refl
leb-n-suc-n (suc n) rewrite leb-n-suc-n n = refl

remove-does-not-increase-count : (s : Bag) → ((count 0 (remove-one 0 s)) <=? (count 0 s)) ≡ true
remove-does-not-increase-count [] = refl
remove-does-not-increase-count (zero ∷ xs) = leb-n-suc-n (count 0 xs)
remove-does-not-increase-count (suc x ∷ xs) = remove-does-not-increase-count xs

bag-count-sum : (n : ℕ) → (xs : Bag) → (ys : Bag) → count n xs + count n ys ≡ count n (app xs ys)
bag-count-sum n [] ys = refl
bag-count-sum n (x ∷ xs) ys with n =? x
... | false = bag-count-sum n xs ys
... | true = cong suc (bag-count-sum n xs ys)

involutive-injective : (f : ℕ → ℕ) →
                       ((n : ℕ) → n ≡ f (f n)) →
                       ((x y : ℕ) → f x ≡ f y → x ≡ y)
involutive-injective f inv x y eq = begin
  x       ≡⟨ inv x ⟩
  f (f x) ≡⟨ cong f eq ⟩
  f (f y) ≡⟨ sym (inv y) ⟩
  y       ∎

involutive-injective' : (f : ℕ → ℕ) →
                        ((n : ℕ) → n ≡ f (f n)) →
                        ((x y : ℕ) → f x ≡ f y → x ≡ y)
involutive-injective' f inv x y eq = trans (inv x) (trans (cong f eq) (sym (inv y)))

involutive-injective-Listℕ : (f : Listℕ → Listℕ) →
                             ((n : Listℕ) → n ≡ f (f n)) →
                             ((x y : Listℕ) → f x ≡ f y → x ≡ y)
involutive-injective-Listℕ f inv x y eq = begin
  x       ≡⟨ inv x ⟩
  f (f x) ≡⟨ cong f eq ⟩
  f (f y) ≡⟨ sym (inv y) ⟩
  y       ∎

private
  rev-involutive' : (xs : Listℕ) → xs ≡ rev (rev xs)
  rev-involutive' xs = sym (rev-involutive xs)

rev-injective : (xs ys : Listℕ) → rev xs ≡ rev ys → xs ≡ ys
rev-injective xs ys eq rewrite involutive-injective-Listℕ rev rev-involutive' xs ys eq = refl

Maybeℕ : Set
Maybeℕ = Maybe ℕ

nth-error : Listℕ → ℕ → Maybeℕ
nth-error [] _ = nothing
nth-error (x ∷ xs) zero = just x
nth-error (x ∷ xs) (suc n) = nth-error xs n

nth-error-test₁ : nth-error (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 0 ≡ just 4
nth-error-test₁ = refl

nth-error-test₂ : nth-error (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 3 ≡ just 7
nth-error-test₂ = refl

nth-error-test₃ : nth-error (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 9 ≡ nothing
nth-error-test₃ = refl

maybe-elim : ℕ → Maybeℕ → ℕ
maybe-elim def (just n) = n
maybe-elim def nothing = def

hd-error : Listℕ → Maybeℕ
hd-error [] = nothing
hd-error (x ∷ _) = just x

test-hd-error₁ : hd-error [] ≡ nothing
test-hd-error₁ = refl

test-hd-error₂ : hd-error (1 ∷ []) ≡ just 1
test-hd-error₂ = refl

test-hd-error₃ : hd-error (5 ∷ 6 ∷ []) ≡ just 5
test-hd-error₃ = refl

maybe-elim-hd : (xs : Listℕ) → (default : ℕ) → hd default xs ≡ maybe-elim default (hd-error xs)
maybe-elim-hd [] default = refl
maybe-elim-hd (x ∷ xs) default = refl

data Id : Set where
  id : ℕ → Id

eqb-id : Id → Id → Bool
eqb-id (id n₁) (id n₂) = n₁ =? n₂

eqb-id-refl : (x : Id) → eqb-id x x ≡ true
eqb-id-refl (id zero) = refl
eqb-id-refl (id (suc x)) = eqb-refl x

module PartialMap where

  data PartialMap : Set where
    empty : PartialMap
    entry : Id → ℕ → PartialMap → PartialMap

  update : PartialMap → Id → ℕ → PartialMap
  update d x value = entry x value d

  find : Id → PartialMap → Maybeℕ
  find x empty = nothing
  find x (entry i v d) with eqb-id x i
  ... | false = find x d
  ... | true = just v

  update-eq : (d : PartialMap) → (x : Id) → (v : ℕ) →
              find x (update d x v) ≡ just v
  update-eq _ (id x) _ rewrite eqb-refl x = refl

  update-neq : (d : PartialMap) → (x y : Id) → (o : ℕ) →
               eqb-id x y ≡ false →
               find x (update d y o) ≡ find x d
  update-neq _ _ _ _ eq rewrite eq = refl
