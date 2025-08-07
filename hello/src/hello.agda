module hello where

-- from Jesper Cockx "Programming and Proving in Agda" (Version of March 18, 2024)

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
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

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

-- 3. The Curry-Howard correspondence

-- Propositional Logic

-- Exercise 3.1

data Either (A : Set) (B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left a) f g = f a
cases (right b) f g = g b

-- Truth
data ⊤ : Set where
  tt : ⊤

-- Falsity
data ⊥ : Set where
  -- no constructors

-- The principle of explosion (also known under the latin name “ex
-- falso quodlibet”, or “from falsity follows anything”) tells us we
-- can can get a proof absurd p of any proposition we want.
--
-- The special pattern () used to indicate this is called an absurd
-- pattern, and the clause is called an absurd clause. Absurd patterns
-- are used to indicate to Agda that there are no possible inputs of a
-- given type, but we cannot just skip the clause since there would be
-- no other clauses left.
absurd : {A : Set} → ⊥ → A
absurd ()

-- P implies P
proof1 : {P : Set} → P → P
proof1 p = p

-- If ((P implies Q) and (Q implies R)) then (P implies R)
proof2 : {P Q R : Set} → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) = λ x -> g (f x)

-- If ((P or Q) implies R) then ((P implies R) and (Q implies R))
proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ y → f (right y))

proof-and-commutative : {P Q : Set} → (P × Q) → (Q × P)
proof-and-commutative (p , q) = q , p

-- Exercise 3.2

-- If A then (B implies A)
proof4 : {A B : Set} → A → (B → A)
proof4 a = λ _ → a

-- If (A and true) then (A or false)
proof5 : {A : Set} → (A × ⊤) → Either A ⊥
proof5 (a , tt) = left a

-- If (A implies (B implies C)), then ((A and B) implies C)
proof6 : {A B C : Set} → (A → (B → C)) → ((A × B) → C)
proof6 f = λ x → (f (fst x)) (snd x)

-- If (A and (B or C)), then either (A and B) or (A and C)
proof7 : {A B C : Set} → (A × Either B C) → Either (A × B) (A × C)
proof7 (a , left b) = left (a  , b)
proof7 (a , right c) = right (a , c)

-- If ((A implies C) and (B implies D)), then ((A and B) implies (C and D))
proof8 : {A B C D : Set} → ((A → C) × (B → D)) → ((A × B) → (C × D))
proof8 (f , g) = λ x → (f (fst x), g (snd x))

-- Exercise 3.2

proof9 : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
proof9 f = f (right (λ p → f (left p)))

-- Predicate Logic

data IsEven : Nat → Set where
  zeroIsEven : IsEven zero
  sucsucIsEven : {n : Nat} → IsEven n → IsEven (suc (suc n))

6-is-even : IsEven 6
6-is-even = sucsucIsEven (sucsucIsEven (sucsucIsEven zeroIsEven))

7-is-not-even : IsEven 7 → ⊥
7-is-not-even (sucsucIsEven (sucsucIsEven (sucsucIsEven ())))

data IsTrue : Bool → Set where
  trueIsTrue : IsTrue true

_=Nat_ : Nat → Nat → Bool
zero =Nat zero = true
zero =Nat suc y = false
suc x =Nat zero = false
suc x =Nat suc y = x =Nat y

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = trueIsTrue

-- Universal and existential quantifiers

double : Nat → Nat
double zero = zero
double (suc n) = suc (suc (double n))

double-is-even : (n : Nat) → IsEven (double n)
double-is-even zero = zeroIsEven
double-is-even (suc m) = sucsucIsEven (double-is-even m)

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero = trueIsTrue
n-equals-n (suc m) = n-equals-n m

half-a-dozen : Σ Nat (λ n → IsTrue ((n + n) =Nat 12))
half-a-dozen = 6 , trueIsTrue

zero-or-suc : (n : Nat) → Either (IsTrue (n =Nat 0)) (Σ Nat (λ m → IsTrue (n =Nat (suc m))))
zero-or-suc zero = left trueIsTrue
zero-or-suc (suc m) = right (m , n-equals-n m)

-- The identity type
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 → ⊥
zero-not-one ()

id-returns-input : {A : Set} → (x : A) → id x ≡ x
id-returns-input x = refl

-- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

module tests where

  4-plus-5 : 4 + 5 ≡ 9
  4-plus-5 = refl

  0-plus-1 : 0 + 1 ≡ 1
  0-plus-1 = refl

  halve-0 : halve 0 ≡ 0
  halve-0 = refl

  halve-1 : halve 1 ≡ 0
  halve-1 = refl

  halve-2 : halve 2 ≡ 1
  halve-2 = refl

  halve-3 : halve 3 ≡ 1
  halve-3 = refl

  halve-4 : halve 4 ≡ 2
  halve-4 = refl

  halve-8 : halve 8 ≡ 4
  halve-8 = refl

  halve-9 : halve 9 ≡ 4
  halve-9 = refl

  halve-23 : halve 23 ≡ 11
  halve-23 = refl

  halve-24 : halve 24 ≡ 12
  halve-24 = refl

  9-times-0 : 9 * 0 ≡ 0
  9-times-0 = refl

  9-times-1 : 9 * 1 ≡ 9
  9-times-1 = refl

  9-times-3 : 9 * 3 ≡ 27
  9-times-3 = refl

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

  _ : toVec (toList' xs) ≡ vs
  _ = refl

  vs' : List' Nat
  vs' = 3 , vs

  _ : toVec vs' ≡ vs
  _ = refl

  _ : fromVec (toVec vs') ≡ vs'
  _ = refl

-- 4. Equational reasoning in Agda

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

-- Simple examples

[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩ -- definition of [_]
    reverse (x :: [])
  =⟨⟩ -- applying reverse (second clause)
    reverse [] ++ [ x ]
  =⟨⟩ -- applying reverse (first clause)
    [] ++ [ x ]
  =⟨⟩ -- applying _++_
    [ x ]
  end

-- Proof by cases and induction

not-not : (b : Bool) → not (not b) ≡ b
not-not false =
  begin
    not (not false)
  =⟨⟩ -- applying the inner not
    not true
  =⟨⟩ -- applying not
    false
  end
not-not true =
  begin
    not (not true)
  =⟨⟩ -- applying the inner not
    not false
  =⟨⟩ -- applying not
    true
  end

add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero =
  begin
    zero + zero
  =⟨⟩ -- applying +
    zero
  end
add-n-zero (suc n) =
  begin
    (suc n) + zero
  =⟨⟩ -- applying +
    suc (n + zero)
  =⟨ cong suc (add-n-zero n) ⟩ -- using induction hypothesis
    suc n
  end

-- Exercise 4.1

add-m-suc-n : (m n : Nat) → m + suc n ≡ suc (m + n)
add-m-suc-n zero n =
  begin
    zero + suc n
  =⟨⟩
    suc n
  =⟨⟩
    suc (zero + n)
  end
add-m-suc-n (suc m) n =
  begin
    suc m + suc n
  =⟨⟩
    suc (m + suc n)
  =⟨ cong suc (add-m-suc-n m n) ⟩
    suc (suc (m + n))
  =⟨⟩
    suc ((suc m) + n)
  end

commutativity-of-add : (m n : Nat) →  m + n ≡ n + m
commutativity-of-add zero n =
  begin
    zero + n
  =⟨⟩
    n
  =⟨ sym (add-n-zero n) ⟩
    n + zero
  end
commutativity-of-add (suc m) n =
  begin
    suc m + n
  =⟨⟩
    suc (m + n)
  =⟨ cong suc (commutativity-of-add m n) ⟩
    suc (n + m)
  =⟨ sym (add-m-suc-n n m) ⟩
    n + suc m
  end

-- Proof that the addition of natural numbers is associative
add-assoc : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
  begin
    zero + (y + z)
  =⟨⟩ -- applying the outer add
    y + z
  =⟨⟩ -- unapplying add
    (zero + y) + z
  end
add-assoc (suc x) y z =
  begin
    (suc x) + (y + z)
  =⟨⟩                             -- applying the outer add
    suc (x + (y + z))
  =⟨ cong suc (add-assoc x y z) ⟩ -- using the induction hypothesis
    suc ((x + y) + z)
  =⟨⟩                             -- unapplying the outer add
    (suc (x + y)) + z
  =⟨⟩                             -- unapplying the outer add
    ((suc x) + y) + z
  end

-- Induction on lists

-- Exercise 4.3
append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] [] =
  begin
    [] ++ []
  =⟨⟩
    []
  end
append-[] (x :: xs) =
  begin
    (x :: xs) ++ []
  =⟨⟩                              -- applying ++
    x :: (xs ++ [])
  =⟨ cong (x ::_) (append-[] xs) ⟩ -- using induction hypothesis
    x :: xs
  end

-- Exercise 4.3
append-assoc : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
append-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  =⟨⟩
    ys ++ zs
  =⟨⟩
    [] ++ (ys ++ zs)
  end
append-assoc (x :: xs) ys zs =
  begin
    ((x :: xs) ++ ys) ++ zs
  =⟨⟩                                       -- applying ++
    (x :: (xs ++ ys)) ++ zs
  =⟨⟩                                       -- applying ++
    x :: ((xs ++ ys) ++ zs)
  =⟨ cong (x ::_) (append-assoc xs ys zs) ⟩ -- using induction hypothesis
    x :: (xs ++ (ys ++ zs))
  =⟨⟩                                       -- unapplying ++
    (x :: xs) ++ (ys ++ zs)
  end

reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] =
  begin
    reverse (reverse [])
  =⟨⟩ -- applying inner reverse
    reverse []
  =⟨⟩ -- applying reverse
    []
  end
reverse-reverse (x :: xs) =
  begin
    reverse (reverse (x :: xs))
  =⟨⟩                                            -- applying the inner reverse
    reverse (reverse xs ++ [ x ])
  =⟨ reverse-distributivity (reverse xs) [ x ] ⟩ -- distributivity (see below)
    reverse [ x ] ++ reverse (reverse xs)
  =⟨⟩                                            -- reverse singleton list
    [ x ] ++ reverse (reverse xs)
  =⟨⟩                                            -- definition of ++
    x :: reverse (reverse xs)
  =⟨ cong (x ::_) (reverse-reverse xs) ⟩         -- using induction hypothesis
    x :: xs
  end
  where
    reverse-distributivity : {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-distributivity [] ys =
      begin
        reverse ([] ++ ys)
      =⟨⟩                                                  -- applying ++
        reverse ys
      =⟨ sym (append-[] (reverse ys)) ⟩                    -- see append-[] lemma
        reverse ys ++ []
      =⟨⟩                                                  -- unapplying reverse
        reverse ys ++ reverse []
      end
    reverse-distributivity (x :: xs) ys =
      begin
        reverse ((x :: xs) ++ ys)
      =⟨⟩                                                  -- applying ++
        reverse (x :: (xs ++ ys))
      =⟨⟩                                                  -- applying reverse
        reverse (xs ++ ys) ++ reverse [ x ]
      =⟨⟩                                                  -- applying reverse
        reverse (xs ++ ys) ++ [ x ]
      =⟨ cong (_++ [ x ]) (reverse-distributivity xs ys) ⟩ -- using induction hypothesis
        (reverse ys ++ reverse xs) ++ [ x ]
      =⟨ append-assoc (reverse ys) (reverse xs) [ x ] ⟩    -- using associativity of ++
        reverse ys ++ (reverse xs ++ [ x ])
      =⟨⟩                                                  -- unapplying inner ++
        reverse ys ++ (reverse (x :: xs))
      end

map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] =
  begin
    map id []
  =⟨⟩                           -- applying map
    []
  end
map-id (x :: xs) =
  begin
    map id (x :: xs)
  =⟨⟩                           -- applying map
    id x :: map id xs
  =⟨⟩                           -- applying id
    x :: map id xs
  =⟨ cong (x ::_) (map-id xs) ⟩ -- using induction hypothesis
    x :: xs
  end

_◦_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ◦ h = λ x → g (h x)

map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A) → map (f ◦ g) xs ≡ map f (map g xs)
map-compose f g [] =
  begin
    map (f ◦ g) []
  =⟨⟩                       -- applying map
    []
  =⟨⟩                       -- unapplying map
    map f []
  =⟨⟩                       -- unapplying map
    map f (map g [])
  end
map-compose f g (x :: xs) =
  begin
    map (f ◦ g) (x :: xs)
  =⟨⟩                                          -- applying map
    (f ◦ g) x :: map (f ◦ g) xs
  =⟨⟩                                          -- applying function composition
    f (g x) :: map (f ◦ g) xs
  =⟨ cong (f (g x) ::_) (map-compose f g xs) ⟩ -- using induction hypothesis
    f (g x) :: map f (map g xs)
  =⟨⟩                                          -- unapplying map
    map f (g x :: map g xs)
  =⟨⟩                                          -- unapplying map
    map f (map g (x :: xs))
  end

-- Exercise 4.4
length-map : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
length-map f [] =
  begin
    length (map f [])
  end
length-map f (x :: xs) =
  begin
    length (map f (x :: xs))
  =⟨⟩                                       -- applying map
    length (f x :: map f xs)
  =⟨⟩                                       -- applying length
    1 + length (map f xs)
  =⟨ cong (λ n → 1 + n) (length-map f xs) ⟩ -- using induction hypothesis
    1 + length xs
  =⟨⟩
    length (x :: xs)
  end

-- Exercise 4.5
take : {A : Set} → (n : Nat) → List A → List A
take n [] = []
take zero _ = []
take (suc n) (x :: xs) = x :: take n xs

drop : {A : Set} → (n : Nat) → List A → List A
drop n [] = []
drop zero xs = xs
drop (suc n) (x :: xs) = drop n xs

take-drop : {A : Set} → (n : Nat) → (xs : List A) → take n xs ++ drop n xs ≡ xs
take-drop n [] =
  begin
    take n [] ++ drop n []
  =⟨⟩                                -- applying take
    [] ++ drop n []
  =⟨⟩                                -- applying drop
    [] ++ []
  =⟨⟩                                -- applying ++
    []
  end
take-drop zero (x :: xs) =
  begin
    take zero (x :: xs) ++ drop zero (x :: xs)
  =⟨⟩                                -- applying take
    [] ++ drop zero (x :: xs)
  =⟨⟩                                -- applying drop
    [] ++ (x :: xs)
  =⟨⟩                                -- applying ++
    (x :: xs)
  end
take-drop (suc n) (x :: xs) =
  begin
    take (suc n) (x :: xs) ++ drop (suc n) (x :: xs)
  =⟨⟩                                -- applying take
    (x :: take n xs) ++ drop (suc n) (x :: xs)
  =⟨⟩                                -- applying drop
    (x :: take n xs) ++ drop n xs
  =⟨⟩                                -- applying ++
    x :: (take n xs ++ drop n xs)
  =⟨ cong (x ::_) (take-drop n xs) ⟩ -- using induction hypothesis
    x :: xs
  end

-- Verifying optimizations

reverse-acc : {A : Set} → List A → List A → List A
reverse-acc [] ys = ys
reverse-acc (x :: xs) ys = reverse-acc xs (x :: ys)

reverse' : {A : Set} → List A → List A
reverse' xs = reverse-acc xs []

reverse'-reverse : {A : Set} → (xs : List A) → reverse' xs ≡ reverse xs
reverse'-reverse xs =
  begin
    reverse' xs
  =⟨⟩                           -- definition of reverse'
    reverse-acc xs []
  =⟨ reverse-acc-lemma xs [] ⟩  -- using reverse-acc-lemma
    reverse xs ++ []
  =⟨ append-[] (reverse xs) ⟩   -- using append-[]
    reverse xs
  end
  where
    reverse-acc-lemma : {A : Set} → (xs ys : List A) → reverse-acc xs ys ≡ reverse xs ++ ys
    reverse-acc-lemma [] ys =
      begin
        reverse-acc [] ys
      =⟨⟩                                           -- definition of reverse-acc
        ys
      =⟨⟩                                           -- unapplying ++
        [] ++ ys
      =⟨⟩                                           -- unapplying reverse
        reverse [] ++ ys
      end
    reverse-acc-lemma (x :: xs) ys =
      begin
        reverse-acc (x :: xs) ys
      =⟨⟩                                           -- definition of reverse-acc
        reverse-acc xs (x :: ys)
      =⟨ reverse-acc-lemma xs (x :: ys) ⟩           -- using induction hypothesis
        reverse xs ++ (x :: ys)
      =⟨⟩                                           -- unapplying ++
        reverse xs ++ ([ x ] ++ ys)
      =⟨ sym (append-assoc (reverse xs) [ x ] ys) ⟩ -- using associativity of append
        (reverse xs ++ [ x ]) ++ ys
      =⟨⟩                                           -- unapplying reverse
        reverse (x :: xs) ++ ys
      end

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

flatten : {A : Set} → Tree A → List A
flatten (leaf x) = [ x ]
flatten (node t1 t2) = flatten t1 ++ flatten t2

flatten-acc : {A : Set} → Tree A → List A → List A
flatten-acc (leaf x) xs = x :: xs
flatten-acc (node t1 t2) xs = flatten-acc t1 (flatten-acc t2 xs)

flatten' : {A : Set} → Tree A → List A
flatten' t = flatten-acc t []

flatten-acc-flatten : {A : Set} (t : Tree A) (xs : List A) → flatten-acc t xs ≡ flatten t ++ xs
flatten-acc-flatten (leaf x) xs =
  begin
    flatten-acc (leaf x) xs
  =⟨⟩                                                  -- definition of flatten-acc
    x :: xs
  =⟨⟩                                                  -- unapplying ++
    [ x ] ++ xs
  =⟨⟩                                                  -- unapplying flatten
    flatten (leaf x) ++ xs
  end
flatten-acc-flatten (node l r) xs =
  begin
    flatten-acc (node l r) xs
  =⟨⟩                                                  -- applying flatten-acc
    flatten-acc l (flatten-acc r xs)
  =⟨ flatten-acc-flatten l (flatten-acc r xs) ⟩        -- using IH for l
    flatten l ++ (flatten-acc r xs)
  =⟨ cong (flatten l ++_) (flatten-acc-flatten r xs) ⟩ -- using IH for r
    flatten l ++ (flatten r ++ xs)
  =⟨ sym (append-assoc (flatten l) (flatten r) xs) ⟩   -- using append-assoc
    (flatten l ++ flatten r) ++ xs
  =⟨⟩
    (flatten (node l r)) ++ xs
  end

-- Exercise 4.6
flatten'-flatten : {A : Set} → (t : Tree A) → flatten' t ≡ flatten t
flatten'-flatten (leaf x) =
  begin
    flatten' (leaf x)
  =⟨⟩                                    -- definition of flatten'
    flatten-acc (leaf x) []
  =⟨⟩                                    -- applying flatten-acc
    x :: []
  =⟨⟩                                    -- applying ++
    [ x ]
  end
flatten'-flatten (node l r) =
  begin
    flatten' (node l r)
  =⟨⟩                                    -- definition of flatten'
    flatten-acc (node l r) []
  =⟨ flatten-acc-flatten (node l r) [] ⟩ -- using flatten-acc-flatten
    flatten (node l r) ++ []
  =⟨ append-[] (flatten (node l r)) ⟩    -- using append-[]
    flatten (node l r)
  end

-- Compiler correctness

data Expr : Set where
  valE : Nat → Expr
  addE : Expr → Expr → Expr

eval : Expr → Nat
eval (valE x) = x
eval (addE e1 e2) = eval e1 + eval e2

data Op  : Set where
  PUSH : Nat → Op
  ADD : Op

Stack = List Nat
Code = List Op

exec : Code → Stack → Stack
exec [] s = s
exec (PUSH x :: c) s = exec c (x :: s)
exec (ADD :: c) (m :: n :: s) = exec c (n + m :: s)
exec (ADD :: c) _ = []

-- First version, inefficient and hard to reason about
-- compile : Expr → Code
-- compile (valE x) = [ PUSH x ]
-- compile (addE e1 e2) = compile e1 ++ compile e2 ++ [ ADD ]

-- Second version, much faster and easier to prove correct
compile' : Expr → Code → Code
compile' (valE x) c = PUSH x :: c
compile' (addE e1 e2) c = compile' e1 (compile' e2 (ADD :: c))

compile : Expr → Code
compile e = compile' e []

compile'-exec-eval : (e : Expr) (s : Stack) (c : Code) → exec (compile' e c) s ≡ exec c (eval e :: s)
compile'-exec-eval (valE x) s c =
  begin
    exec (compile' (valE x) c) s
  =⟨⟩                                                   -- applying compile'
    exec (PUSH x :: c) s
  =⟨⟩                                                   -- applying exec for PUSH
    exec c (x :: s)
  =⟨⟩                                                   -- unapplying eval for valE
    exec c (eval (valE x) :: s)
  end
compile'-exec-eval (addE e1 e2) s c =
  begin
    exec (compile' (addE e1 e2) c) s
  =⟨⟩                                                   -- applying compile'
    exec (compile' e1 (compile' e2 (ADD :: c))) s
  =⟨ compile'-exec-eval e1 s (compile' e2 (ADD :: c)) ⟩ -- using IH for e1
    exec (compile' e2 (ADD :: c)) (eval e1 :: s)
  =⟨ compile'-exec-eval e2 (eval e1 :: s) (ADD :: c)⟩   -- using IH for e2
    exec (ADD :: c) (eval e2 :: eval e1 :: s)
  =⟨⟩                                                   -- applying exec for ADD
    exec c (eval e1 + eval e2 :: s)
  =⟨⟩                                                   -- unapplying eval for addE
    exec c (eval (addE e1 e2) :: s)
  end

compile-exec-eval : (e : Expr) → exec (compile e) [] ≡ [ eval e ]
compile-exec-eval e =
  begin
    exec (compile e) []
  =⟨ compile'-exec-eval e [] [] ⟩ -- using compile'-exec-eval lemma
    exec [] (eval e :: [])
  =⟨⟩                             -- unapplying exec for []
    eval e :: []
  =⟨⟩                             -- unapplying [_]
    [ eval e ]
  end
