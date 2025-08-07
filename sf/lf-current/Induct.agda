module lf-current.Induct where

open import Agda.Builtin.Nat
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import lf-current.Basics

add-0-r : (n : Nat) → n + 0 ≡ n
add-0-r 0 = refl
add-0-r (suc n) rewrite add-0-r n = refl

minus : Nat → Nat → Nat
minus = NatPlayground2.minus

minus-n-n : (n : Nat) → minus n n ≡ 0
minus-n-n zero = refl
minus-n-n (suc n) rewrite minus-n-n n = refl

mul-0-r : (n : Nat) → n * 0 ≡ 0
mul-0-r zero = refl
mul-0-r (suc n) rewrite mul-0-r n = refl

plus-n-Sm : (n m : Nat) → suc (n + m) ≡ n + suc m
plus-n-Sm zero m = refl
plus-n-Sm (suc n) m = cong suc (plus-n-Sm n m)

open ≡-Reasoning

plus-n-Sm' : (n m : Nat) → suc (n + m) ≡ n + suc m
plus-n-Sm' zero m = begin
  zero + suc m   ≡⟨⟩
  suc m          ≡⟨⟩
  suc (zero + m) ∎
plus-n-Sm' (suc n) m = begin
  suc ((suc n) + m) ≡⟨⟩
  suc (suc (n + m)) ≡⟨ cong suc (plus-n-Sm' n m) ⟩
  suc (n + suc m)   ≡⟨⟩
  suc n + suc m     ∎

add-comm : (n m : Nat) → n + m ≡ m + n
add-comm zero m rewrite add-0-r m = refl
add-comm (suc n) m rewrite add-comm n m | plus-n-Sm m n = refl

add-assoc : (n m p : Nat) → n + (m + p) ≡ (n + m) + p
add-assoc zero m p = refl
add-assoc (suc n) m p rewrite add-assoc n m p = refl

double : Nat -> Nat
double zero = zero
double (suc n) = suc (suc (double n))

double-plus : (n : Nat) → double n ≡ n + n
double-plus zero = refl
double-plus (suc n) rewrite double-plus n | plus-n-Sm n n = refl

eqb-refl : (n : Nat) → (n =? n) ≡ true
eqb-refl zero = refl
eqb-refl (suc n) rewrite eqb-refl n = refl

even-S : (n : Nat) → even (suc n) ≡ negb (even n)
even-S zero = refl
even-S (suc n) rewrite even-S n | negb-involutive (even n) = refl

private
  add-0-0-r : (n : Nat) → n + 0 + 0 ≡ n
  add-0-0-r n rewrite add-comm n 0 | add-comm n 0 = refl

mult-0-plus : (n m : Nat) → (n + 0 + 0) * m ≡ n * m
mult-0-plus n m rewrite add-0-0-r n = refl

plus-rearrange : (n m p q : Nat) → (n + m) + (p + q) ≡ (m + n) + (p + q)
plus-rearrange n m p q rewrite add-comm n m = refl

add-shuffle : (n m p : Nat) → n + (m + p) ≡ m + (n + p)
add-shuffle n m p rewrite
    add-assoc n m p
  | add-comm n m
  | add-assoc m n p = refl

add-shuffle' : (n m p : Nat) → n + (m + p) ≡ m + (n + p)
add-shuffle' zero m p = refl
add-shuffle' (suc n) m p rewrite add-shuffle n m p | plus-n-Sm m (n + p) = refl

mul-comm : (n m : Nat) → n * m ≡ m * n
mul-comm zero m rewrite mul-0-r m = refl
mul-comm (suc n) m rewrite
    mul-comm n m
  | add-comm m (m * n)
  | mult-n-Sm m n = refl

mul-comm' : (n m : Nat) → n * m ≡ m * n
mul-comm' zero m rewrite mul-0-r m = refl
mul-comm' (suc n) m rewrite
    sym (mult-n-Sm m n)
  | mul-comm n m
  | add-comm m (m * n) = refl

plus-leb-compat-l : (n m p : Nat) → n <=? m ≡ true → (p + n) <=? (p + m) ≡ true
plus-leb-compat-l n m zero H rewrite H = refl
plus-leb-compat-l n m (suc p) H rewrite plus-leb-compat-l n m p H = refl

leb-refl : (n : Nat) → (n <=? n) ≡ true
leb-refl zero = refl
leb-refl (suc n) rewrite leb-refl n = refl

zero-neqb-suc : (n : Nat) → 0 =? (suc n) ≡ false
zero-neqb-suc _ = refl

andb-false-r : (b : Bool) → andb b false ≡ false
andb-false-r true = refl
andb-false-r false = refl

suc-neqb-0 : (n : Nat) → (suc n) =? 0 ≡ false
suc-neqb-0 _ = refl

mult-1-l : (n : Nat) → (1 * n) ≡ n
mult-1-l zero = refl
mult-1-l (suc n) rewrite mult-1-l n = refl

all3-spec : (b c : Bool) → orb (andb b c) (orb (negb b) (negb c)) ≡ true
all3-spec true true = refl
all3-spec true false = refl
all3-spec false c = refl

mult-plus-distr-r : (n m p : Nat) → (n + m) * p ≡ (n * p) + (m * p)
mult-plus-distr-r n m zero rewrite
    mul-0-r n
  | mul-0-r m
  | mul-0-r (n + m)
  = refl
mult-plus-distr-r n m (suc p) rewrite
    sym (mult-n-Sm (n + m) p)
  | mult-plus-distr-r n m p
  | sym (add-assoc (n * p) (m * p) (n + m))
  | add-assoc (m * p) n m
  | add-comm (m * p) n
  | sym (add-assoc n (m * p) m)
  | add-assoc (n * p) n (m * p + m)
  | sym (mult-n-Sm n p)
  | sym (mult-n-Sm m p)
  = refl

mult-plus-distr-r' : (n m p : Nat) → (n + m) * p ≡ (n * p) + (m * p)
mult-plus-distr-r' n m zero = begin
  (n + m) * zero      ≡⟨ mul-0-r (n + m) ⟩
  zero                ≡⟨⟩
  zero + zero         ≡⟨ sym (cong₂ _+_ (mul-0-r n) (mul-0-r m)) ⟩
  n * zero + m * zero ∎
mult-plus-distr-r' n m (suc p) = begin
  (n + m) * suc p           ≡⟨ sym (mult-n-Sm (n + m) p) ⟩
  (n + m) * p + (n + m)     ≡⟨ cong (_+ (n + m)) (mult-plus-distr-r n m p) ⟩
  (n * p + m * p) + (n + m) ≡⟨ sym (add-assoc (n * p) (m * p) (n + m)) ⟩
  n * p + (m * p + (n + m)) ≡⟨ cong (n * p +_) (add-assoc (m * p) n m) ⟩
  n * p + ((m * p + n) + m) ≡⟨ cong (n * p +_) (cong (_+ m) (add-comm (m * p) n)) ⟩
  n * p + ((n + m * p) + m) ≡⟨ cong (n * p +_) (sym (add-assoc n (m * p) m)) ⟩
  n * p + (n + (m * p + m)) ≡⟨ add-assoc (n * p) n (m * p + m) ⟩
  (n * p + n) + (m * p + m) ≡⟨ cong₂ _+_ (mult-n-Sm n p) (mult-n-Sm m p) ⟩
  n * suc p + m * suc p     ∎

mult-assoc : (n m p : Nat) → n * (m * p) ≡ (n * m) * p
mult-assoc zero m p = refl
mult-assoc (suc n) m p = begin
  suc n * (m * p)       ≡⟨⟩
  (m * p) + n * (m * p) ≡⟨ cong ((m * p) +_) (mult-assoc n m p) ⟩
  (m * p) + (n * m) * p ≡⟨ sym (mult-plus-distr-r m (n * m) p) ⟩
  (m + n * m) * p       ≡⟨⟩
  (suc n * m) * p       ∎

mult-assoc' : (n m p : Nat) → n * (m * p) ≡ (n * m) * p
mult-assoc' zero m p = refl
mult-assoc' (suc n) m p rewrite
    mult-assoc n m p
  | mult-plus-distr-r m (n * m) p
  = refl

add-shuffle3 : (n m p : Nat) → n + (m + p) ≡ m + (n + p)
add-shuffle3 n m p rewrite
    add-assoc n m p
  | add-assoc m n p
  | add-comm n m
  = refl

bin-to-nat-pres-incr : (b : Bin) → bin-to-nat (incr b) ≡ 1 + bin-to-nat b
bin-to-nat-pres-incr Z = refl
bin-to-nat-pres-incr (B0 b) = add-comm (2 * bin-to-nat b) 1
bin-to-nat-pres-incr (B1 b) = begin
  bin-to-nat (B0 (incr b))   ≡⟨⟩
  2 * bin-to-nat (incr b)    ≡⟨ cong (2 *_) (bin-to-nat-pres-incr b) ⟩
  2 * (1 + bin-to-nat b)     ≡⟨ mul-comm 2 (1 + bin-to-nat b) ⟩
  (1 + bin-to-nat b) * 2     ≡⟨ mult-plus-distr-r 1 (bin-to-nat b) 2 ⟩
  1 * 2 + bin-to-nat b * 2   ≡⟨ cong₂ _+_ (mult-1-l 2) (mul-comm (bin-to-nat b) 2) ⟩
  2 + 2 * bin-to-nat b       ≡⟨⟩
  suc (1 + 2 * bin-to-nat b) ≡⟨ cong suc (add-comm 1 (2 * bin-to-nat b)) ⟩
  suc (2 * bin-to-nat b + 1) ≡⟨⟩
  1 + (2 * bin-to-nat b + 1) ∎

nat-to-bin : Nat -> Bin
nat-to-bin zero = Z
nat-to-bin (suc n) = incr (nat-to-bin n)

nat-bin-nat : (n : Nat) → bin-to-nat (nat-to-bin n) ≡ n
nat-bin-nat zero = refl
nat-bin-nat (suc n) rewrite bin-to-nat-pres-incr (nat-to-bin n) | nat-bin-nat n = refl

double-incr : (n : Nat) → double (suc n) ≡ suc (suc (double n))
double-incr _ = refl

double-bin : Bin → Bin
double-bin Z = Z
double-bin (B0 b) = B0 (B0 b)
double-bin (B1 b) = B0 (B1 b)

double-bin-zero : double-bin Z ≡ Z
double-bin-zero = refl

double-incr-bin : (b : Bin) → double-bin (incr b) ≡ incr (incr (double-bin b))
double-incr-bin Z = refl
double-incr-bin (B0 b) = refl
double-incr-bin (B1 b) = refl

normalize : Bin → Bin
normalize Z = Z
normalize (B0 b) = double-bin (normalize b)
normalize (B1 b) = incr (double-bin (normalize b))

normalize-B0-Z : normalize (B0 Z) ≡ Z
normalize-B0-Z = refl

normalize-B0-B0-Z : normalize (B0 (B0 Z)) ≡ Z
normalize-B0-B0-Z = refl

normalize-B0-B1-Z : normalize (B0 (B1 Z)) ≡ B0 (B1 Z)
normalize-B0-B1-Z = refl

normalize-B1-B0-Z : normalize (B1 (B0 Z)) ≡ B1 Z
normalize-B1-B0-Z = refl

normalize-B1-B1-Z : normalize (B1 (B1 Z)) ≡ B1 (B1 Z)
normalize-B1-B1-Z = refl

normalize-B0-B0-B0-Z : normalize (B0 (B0 (B0 Z))) ≡ Z
normalize-B0-B0-B0-Z = refl

normalize-B0-B1-B0-Z : normalize (B0 (B1 (B0 Z))) ≡ B0 (B1 Z)
normalize-B0-B1-B0-Z = refl

normalize-B1-B0-B1-Z : normalize (B1 (B0 (B1 Z))) ≡ B1 (B0 (B1 Z))
normalize-B1-B0-B1-Z = refl

normalize-B1-B0-B0-Z : normalize (B1 (B0 (B0 Z))) ≡ B1 Z
normalize-B1-B0-B0-Z = refl

normalize-already-normalized : normalize (B1 (B0 (B1 Z))) ≡ B1 (B0 (B1 Z))
normalize-already-normalized = refl

private
  2*n≡n+n : (n : Nat) → 2 * n ≡ n + n
  2*n≡n+n n = cong (n +_) (mult-1-l n)

  nat-to-bin-double : (n : Nat) → nat-to-bin (double n) ≡ double-bin (nat-to-bin n)
  nat-to-bin-double zero = refl
  nat-to-bin-double (suc n) = begin
    nat-to-bin (double (suc n))             ≡⟨⟩
    nat-to-bin (suc (suc (double n)))       ≡⟨⟩
    incr (nat-to-bin (suc (double n)))      ≡⟨⟩
    incr (incr (nat-to-bin (double n)))     ≡⟨ cong (incr ∘ incr) (nat-to-bin-double n) ⟩
    incr (incr (double-bin (nat-to-bin n))) ≡⟨ sym (double-incr-bin (nat-to-bin n)) ⟩
    double-bin (incr (nat-to-bin n))        ≡⟨⟩
    double-bin (nat-to-bin (suc n))         ∎

bin-nat-bin : (b : Bin) → nat-to-bin (bin-to-nat b) ≡ normalize b
bin-nat-bin Z = refl
bin-nat-bin (B0 b) = begin
  nat-to-bin (bin-to-nat (B0 b))           ≡⟨⟩
  nat-to-bin (2 * bin-to-nat b)            ≡⟨ cong nat-to-bin (2*n≡n+n (bin-to-nat b)) ⟩
  nat-to-bin (bin-to-nat b + bin-to-nat b) ≡⟨ cong nat-to-bin (sym (double-plus (bin-to-nat b))) ⟩
  nat-to-bin (double (bin-to-nat b))       ≡⟨ nat-to-bin-double (bin-to-nat b) ⟩
  double-bin (nat-to-bin (bin-to-nat b))   ≡⟨ cong double-bin (bin-nat-bin b) ⟩
  double-bin (normalize b)                 ≡⟨⟩
  normalize (B0 b)                         ∎
bin-nat-bin (B1 b) = begin
  nat-to-bin (bin-to-nat (B1 b))                 ≡⟨⟩
  nat-to-bin (2 * bin-to-nat b + 1)              ≡⟨ cong nat-to-bin (cong (_+ 1) (2*n≡n+n (bin-to-nat b))) ⟩
  nat-to-bin (bin-to-nat b + bin-to-nat b + 1)   ≡⟨ cong nat-to-bin (add-comm (bin-to-nat b + bin-to-nat b) 1) ⟩
  nat-to-bin (1 + (bin-to-nat b + bin-to-nat b)) ≡⟨ cong nat-to-bin (cong (1 +_) (sym (double-plus (bin-to-nat b)))) ⟩
  nat-to-bin (1 + double (bin-to-nat b))         ≡⟨⟩
  nat-to-bin (suc (double (bin-to-nat b)))       ≡⟨⟩
  incr (nat-to-bin (double (bin-to-nat b)))      ≡⟨ cong incr (nat-to-bin-double (bin-to-nat b)) ⟩
  incr (double-bin (nat-to-bin (bin-to-nat b)))  ≡⟨ cong (incr ∘ double-bin) (bin-nat-bin b) ⟩
  incr (double-bin (normalize b))                ≡⟨⟩
  normalize (B1 b)                               ∎

private
  nat-to-bin-double' : (n : Nat) → nat-to-bin (double n) ≡ double-bin (nat-to-bin n)
  nat-to-bin-double' zero = refl
  nat-to-bin-double' (suc n) rewrite
      nat-to-bin-double' n
    | sym (double-incr-bin (nat-to-bin n)) = refl

bin-nat-bin' : (b : Bin) → nat-to-bin (bin-to-nat b) ≡ normalize b
bin-nat-bin' Z = refl
bin-nat-bin' (B0 b) rewrite
    2*n≡n+n (bin-to-nat b)
  | sym (double-plus (bin-to-nat b))
  | nat-to-bin-double' (bin-to-nat b)
  | bin-nat-bin' b = refl
bin-nat-bin' (B1 b) rewrite
    2*n≡n+n (bin-to-nat b)
  | add-comm (bin-to-nat b + bin-to-nat b) 1
  | sym (double-plus (bin-to-nat b))
  | nat-to-bin-double' (bin-to-nat b)
  | bin-nat-bin' b = refl
