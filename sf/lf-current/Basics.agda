module lf-current.Basics where

open import Data.Nat using (ℕ; suc; zero; _*_; _+_; _∸_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc)
open import Relation.Binary.PropositionalEquality

data Day : Set where
  monday : Day
  tuesday : Day
  wednesday : Day
  thursday : Day
  friday : Day
  saturday : Day
  sunday : Day

next-working-day : Day → Day
next-working-day monday = tuesday
next-working-day tuesday = wednesday
next-working-day wednesday = thursday
next-working-day thursday = friday
next-working-day friday = monday
next-working-day saturday = monday
next-working-day sunday = monday

test-next-working-day : next-working-day (next-working-day saturday) ≡ tuesday
test-next-working-day = refl

negb : Bool → Bool
negb = not

andb : Bool → Bool → Bool
andb = _∧_

orb : Bool → Bool → Bool
orb = _∨_

test-orb₁ : orb true false ≡ true
test-orb₁ = refl

test-orb₂ : orb false false ≡ false
test-orb₂ = refl

test-orb₃ : orb false true ≡ true
test-orb₃ = refl

test-orb₄ : orb true true ≡ true
test-orb₄ = refl

test-orb₅ : (false ∨ false) ∨ true ≡ true
test-orb₅ = refl

data BW : Set where
  bw-black : BW
  bw-white : BW

invert : BW → BW
invert bw-black = bw-white
invert bw-white = bw-black

nandb : Bool → Bool → Bool
nandb true b₂ = negb b₂
nandb false b₂ = true

test-nandb₁ : nandb true false ≡ true
test-nandb₁ = refl

test-nandb₂ : nandb false false ≡ true
test-nandb₂ = refl

test-nandb₃ : nandb false true ≡ true
test-nandb₃ = refl

test-nandb₄ : nandb true true ≡ false
test-nandb₄ = refl

andb3 : Bool → Bool → Bool → Bool
andb3 true b₂ b₃ = andb b₂ b₃
andb3 false b₂ b₃ = false

test-andb3₁ : andb3 true true true ≡ true
test-andb3₁ = refl

test-andb3₂ : andb3 false true true ≡ false
test-andb3₂ = refl

test-andb3₃ : andb3 true false true ≡ false
test-andb3₃ = refl

test-andb3₄ : andb3 true true false ≡ false
test-andb3₄ = refl

data RGB : Set where
  red : RGB
  green : RGB
  blue : RGB

data Color : Set where
  black : Color
  white : Color
  primary : RGB → Color

monochrome : Color → Bool
monochrome black = true
monochrome white = true
monochrome (primary p) = false

isred : Color → Bool
isred black = false
isred white = false
isred (primary red) = true
isred (primary _) = false

module Playground where
  foo : RGB
  foo = blue

foo : Bool
foo = true

module TuplePlayground where

  data Bit : Set where
    B1 : Bit
    B0 : Bit

  data Nybble : Set where
    bits : Bit → Bit → Bit → Bit → Nybble

  all-zero : Nybble → Bool
  all-zero (bits B0 B0 B0 B0) = true
  all-zero (bits _ _ _ _) = false

minustwo : ℕ → ℕ
minustwo 0 = 0
minustwo 1 = 0
minustwo (suc (suc n')) = n'

even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n')) = even n'

odd : ℕ → Bool
odd n = negb (even n)

test-odd₁ : odd 1 ≡ true
test-odd₁ = refl

test-odd₂ : odd 4 ≡ false
test-odd₂ = refl

exp : ℕ → ℕ → ℕ
exp base 0 = 1
exp base (suc p) = base * (exp base p)

factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc n') = (suc n') * (factorial n')

test-factorial₁ : factorial 3 ≡ 6
test-factorial₁ = refl

test-factorial₂ : factorial 5 ≡ (10 * 12)
test-factorial₂ = refl

eqb : ℕ → ℕ → Bool
eqb 0 0 = true
eqb 0 (suc m') = false
eqb (suc n') 0 = false
eqb (suc n') (suc m') = eqb n' m'

leb : ℕ → ℕ → Bool
leb 0 m = true
leb (suc n') 0 = false
leb (suc n') (suc m') = leb n' m'

test-leb₁ : leb 2 2 ≡ true
test-leb₁ = refl

test-leb₂ : leb 2 4 ≡ true
test-leb₂ = refl

test-leb₃ : leb 4 2 ≡ false
test-leb₃ = refl

_=?_ : ℕ → ℕ → Bool
_=?_ = eqb

_<=?_ : ℕ → ℕ → Bool
_<=?_ = leb

test-leb₃' : (4 <=? 2) ≡ false
test-leb₃' = refl

ltb : ℕ → ℕ → Bool
ltb n m with m ∸ n
... | 0 = false
... | _ = true

_<?_ : ℕ → ℕ → Bool
_<?_ = ltb

test-ltb₁ : ltb 2 2 ≡ false
test-ltb₁ = refl

test-ltb₂ : ltb 2 4 ≡ true
test-ltb₂ = refl

test-ltb₃ : ltb 4 2 ≡ false
test-ltb₃ = refl

plus-O-n : (n : ℕ) → 0 + n ≡ n
plus-O-n n = refl

plus-O-n' : (n : ℕ) → 0 + n ≡ n
plus-O-n' n = refl

plus-O-n'' : (n : ℕ) → 0 + n ≡ n
plus-O-n'' m = refl

plus-1-l : (n : ℕ) → 1 + n ≡ suc n
plus-1-l n = refl

mult-0-l : (n : ℕ) → 0 * n ≡ 0
mult-0-l n = refl

plus-id-example : (n m : ℕ) → n ≡ m → n + n ≡ m + m
plus-id-example n m refl = refl

plus-id-exercise : (n m o : ℕ) → n ≡ m → m ≡ o → n + m ≡ m + o
plus-id-exercise n m o refl refl = refl

mult-n-0 : (n : ℕ) → n * 0 ≡ 0
mult-n-0 0 = refl
mult-n-0 (suc n) = mult-n-0 n

-- mult-n-suc-m : (n m : ℕ) → n * m + n ≡ n * suc m
-- mult-n-suc-m 0 m = refl
-- mult-n-suc-m (suc n) m rewrite
--     +-assoc m (n * m) (suc n)
--   | +-suc (n * m) n
--   | mult-n-suc-m n m
--   | sym (+-suc m (n * suc m)) = refl

mult-n-suc-m : (n m : ℕ) → n * m + n ≡ n * suc m
mult-n-suc-m 0 m = refl
mult-n-suc-m (suc n) m = begin
  (suc n) * m + suc n ≡⟨⟩
  (m + n * m) + suc n ≡⟨ +-assoc m (n * m) (suc n) ⟩
  m + (n * m + suc n) ≡⟨ cong (m +_) (+-suc (n * m) n) ⟩
  m + suc (n * m + n) ≡⟨ cong (m +_) (cong suc (mult-n-suc-m n m)) ⟩
  m + suc (n * suc m) ≡⟨ +-suc m (n * suc m) ⟩
  suc (m + n * suc m) ≡⟨⟩
  (suc n) * suc m     ∎
  where open ≡-Reasoning

mult-n-0-m-0 : (p q : ℕ) → (p * 0) + (q * 0) ≡ 0
mult-n-0-m-0 p q rewrite mult-n-0 p | mult-n-0 q = refl

mult-n-1 : (p : ℕ) → p * 1 ≡ p
mult-n-1 0 = refl
mult-n-1 (suc p) rewrite mult-n-1 p = refl

plus-1-neq-0 : (n : ℕ) → ((n + 1) =? 0) ≡ false
plus-1-neq-0 0 = refl
plus-1-neq-0 (suc n') = refl

negb-involutive : (b : Bool) → negb (negb b) ≡ b
negb-involutive true = refl
negb-involutive false = refl

andb-commutative : (b c : Bool) → andb b c ≡ andb c b
andb-commutative true true = refl
andb-commutative true false = refl
andb-commutative false true = refl
andb-commutative false false = refl

andb3-exchange : (b c d : Bool) → andb (andb b c) d ≡ andb (andb b d) c
andb3-exchange true true true = refl
andb3-exchange true true false = refl
andb3-exchange true false true = refl
andb3-exchange true false false = refl
andb3-exchange false true true = refl
andb3-exchange false true false = refl
andb3-exchange false false true = refl
andb3-exchange false false false = refl

andb-true-elim2 : (b c : Bool) → andb b c ≡ true → c ≡ true
andb-true-elim2 true true refl = refl
andb-true-elim2 false true ()
andb-true-elim2 true false ()
andb-true-elim2 false false ()

plus-1-neq-0' : (n : ℕ) → (n + 1) =? 0 ≡ false
plus-1-neq-0' 0 = refl
plus-1-neq-0' (suc n) = refl

andb-commutative'' : (b c : Bool) → andb b c ≡ andb c b
andb-commutative'' true true = refl
andb-commutative'' true false = refl
andb-commutative'' false true = refl
andb-commutative'' false false = refl

zero-nbeq-plus-1 : (n : ℕ) → (0 =? (n + 1)) ≡ false
zero-nbeq-plus-1 0 = refl
zero-nbeq-plus-1 (suc n) = refl

identity-fn-applied-twice : (f : Bool → Bool) →
                            ((x : Bool) → f x ≡ x) →
                            (b : Bool) → f (f b) ≡ b
identity-fn-applied-twice f H b rewrite H (f b) | H b = refl

negation-fn-applied-twice : (f : Bool → Bool) →
                            ((x : Bool) → f x ≡ negb x) →
                            (b : Bool) → f (f b) ≡ b
negation-fn-applied-twice f H true rewrite H true | H false = refl
negation-fn-applied-twice f H false rewrite H false | H true = refl

andb-eq-orb : (b c : Bool) → (andb b c ≡ orb b c) → b ≡ c
andb-eq-orb true c H = sym H
andb-eq-orb false c H = H

module LateDays where

  data Letter : Set where
    A : Letter
    B : Letter
    C : Letter
    D : Letter
    F : Letter

  data Modifier : Set where
    Plus : Modifier
    Natural : Modifier
    Minus : Modifier

  data Grade : Set where
    grade : Letter → Modifier → Grade

  data Comparison : Set where
    Eq : Comparison
    Lt : Comparison
    Gt : Comparison

  letter-comparison : Letter → Letter → Comparison
  letter-comparison A A = Eq
  letter-comparison A _ = Gt
  letter-comparison B A = Lt
  letter-comparison B B = Eq
  letter-comparison B _ = Gt
  letter-comparison C A = Lt
  letter-comparison C B = Lt
  letter-comparison C C = Eq
  letter-comparison C _ = Gt
  letter-comparison D A = Lt
  letter-comparison D B = Lt
  letter-comparison D C = Lt
  letter-comparison D D = Eq
  letter-comparison D _ = Gt
  letter-comparison F A = Lt
  letter-comparison F B = Lt
  letter-comparison F C = Lt
  letter-comparison F D = Lt
  letter-comparison F F = Eq

  letter-comparison-Eq : (l : Letter) → letter-comparison l l ≡ Eq
  letter-comparison-Eq A = refl
  letter-comparison-Eq B = refl
  letter-comparison-Eq C = refl
  letter-comparison-Eq D = refl
  letter-comparison-Eq F = refl

  modifier-comparison : Modifier → Modifier → Comparison
  modifier-comparison Plus Plus = Eq
  modifier-comparison Plus _ = Gt
  modifier-comparison Natural Plus = Lt
  modifier-comparison Natural Natural = Eq
  modifier-comparison Natural _ = Gt
  modifier-comparison Minus Plus = Lt
  modifier-comparison Minus Natural = Lt
  modifier-comparison Minus Minus = Eq

  grade-comparison : Grade → Grade → Comparison
  grade-comparison (grade g1 m1) (grade g2 m2) with letter-comparison g1 g2
  ... | Eq = modifier-comparison m1 m2
  ... | x = x

  test-grade-comparison₁ : grade-comparison (grade A Minus) (grade B Plus) ≡ Gt
  test-grade-comparison₁ = refl

  test-grade-comparison₂ : grade-comparison (grade A Minus) (grade A Plus) ≡ Lt
  test-grade-comparison₂ = refl

  test-grade-comparison₃ : grade-comparison (grade F Plus) (grade F Plus) ≡ Eq
  test-grade-comparison₃ = refl

  test-grade-comparison₄ : grade-comparison (grade B Minus) (grade C Plus) ≡ Gt
  test-grade-comparison₄ = refl

  lower-letter : Letter → Letter
  lower-letter A = B
  lower-letter B = C
  lower-letter C = D
  lower-letter D = F
  lower-letter F = F

  lower-letter-F-is-F : lower-letter F ≡ F
  lower-letter-F-is-F = refl

  lower-letter-lowers : (l : Letter) → letter-comparison F l ≡ Lt →
                        letter-comparison (lower-letter l) l ≡ Lt
  lower-letter-lowers A H = refl
  lower-letter-lowers B H = refl
  lower-letter-lowers C H = refl
  lower-letter-lowers D H = refl
  lower-letter-lowers F ()

  lower-grade : Grade → Grade
  lower-grade (grade g Plus) = grade g Natural
  lower-grade (grade g Natural) = grade g Minus
  lower-grade (grade F Minus) = grade F Minus
  lower-grade (grade g' Minus) = grade (lower-letter g') Plus

  lower-grade-A-Plus : lower-grade (grade A Plus) ≡ grade A Natural
  lower-grade-A-Plus = refl

  lower-grade-A-Natural : lower-grade (grade A Natural) ≡ grade A Minus
  lower-grade-A-Natural = refl

  lower-grade-A-Minus : lower-grade (grade A Minus) ≡ grade B Plus
  lower-grade-A-Minus = refl

  lower-grade-B-Plus : lower-grade (grade B Plus) ≡ grade B Natural
  lower-grade-B-Plus = refl

  lower-grade-F-Natural : lower-grade (grade F Natural) ≡ grade F Minus
  lower-grade-F-Natural = refl

  lower-grade-twice : lower-grade (lower-grade (grade B Minus)) ≡ grade C Natural
  lower-grade-twice = refl

  lower-grade-thrice : lower-grade (lower-grade (lower-grade (grade B Minus))) ≡ grade C Minus
  lower-grade-thrice = refl

  lower-grade-F-Minus : lower-grade (grade F Minus) ≡ grade F Minus
  lower-grade-F-Minus = refl

  lower-grade-lowers : (g : Grade) →
                       grade-comparison (grade F Minus) g ≡ Lt →
                       grade-comparison (lower-grade g) g ≡ Lt
  lower-grade-lowers (grade l Plus) H rewrite letter-comparison-Eq l = refl
  lower-grade-lowers (grade l Natural) H rewrite letter-comparison-Eq l = refl
  lower-grade-lowers (grade A Minus) H = refl
  lower-grade-lowers (grade B Minus) H = refl
  lower-grade-lowers (grade C Minus) H = refl
  lower-grade-lowers (grade D Minus) H = refl
  lower-grade-lowers (grade F Minus) ()

  apply-late-policy : ℕ → Grade → Grade
  apply-late-policy late-days g with late-days <? 9
  ... | true = g
  ... | false with late-days <? 17
  ... | true = lower-grade g
  ... | false with late-days <? 21
  ... | true = lower-grade (lower-grade g)
  ... | false = lower-grade (lower-grade (lower-grade g))

  no-penalty-for-mostly-on-time : (late-days : ℕ) (g : Grade) →
                                  (late-days <? 9) ≡ true →
                                  apply-late-policy late-days g ≡ g
  no-penalty-for-mostly-on-time late-days g H rewrite H = refl

  grade-lowered-once : (late-days : ℕ) (g : Grade) →
                       (late-days <? 9) ≡ false →
                       (late-days <? 17) ≡ true →
                       apply-late-policy late-days g ≡ lower-grade g
  grade-lowered-once late-days g H1 H2 rewrite H1 | H2 = refl

data Bin : Set where
  Z : Bin
  B0 : Bin → Bin
  B1 : Bin → Bin

incr : Bin → Bin
incr Z = B1 Z
incr (B0 n) = B1 n
incr (B1 n) = B0 (incr n)

bin-to-nat : Bin → ℕ
bin-to-nat Z = 0
bin-to-nat (B0 n) = 2 * bin-to-nat n
bin-to-nat (B1 n) = 2 * bin-to-nat n + 1

test-bin-incr₁ : incr (B1 Z) ≡ B0 (B1 Z)
test-bin-incr₁ = refl

test-bin-incr₂ : incr (B0 (B1 Z)) ≡ B1 (B1 Z)
test-bin-incr₂ = refl

test-bin-incr₃ : incr (B1 (B1 Z)) ≡ B0 (B0 (B1 Z))
test-bin-incr₃ = refl

test-bin-incr₄ : bin-to-nat (B0 (B1 Z)) ≡ 2
test-bin-incr₄ = refl

test-bin-incr₅ : bin-to-nat (incr (B1 Z)) ≡ 1 + bin-to-nat (B1 Z)
test-bin-incr₅ = refl

test-bin-incr₆ : bin-to-nat (incr (incr (B1 Z))) ≡ 2 + bin-to-nat (B1 Z)
test-bin-incr₆ = refl
