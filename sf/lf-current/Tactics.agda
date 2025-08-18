module lf-current.Tactics where

open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import lf-current.Basics using (even; odd; minustwo; _=?_)
open import lf-current.Induct using (plus-n-suc-m; mult-1-l; double)
open import lf-current.Lists using (pred)
open import lf-current.Poly using (length; nth-error; rev; rev-involutive)

silly₁ : (n m : ℕ) → n ≡ m → n ≡ m
silly₁ n m eq = eq

silly₂ : (n m o p : ℕ) →
         n ≡ m →
         (n ≡ m → n ∷ o ∷ [] ≡ m ∷ p ∷ []) →
         n ∷ o ∷ [] ≡ m ∷ p ∷ []
silly₂ n m o p eq₁ eq₂ = eq₂ eq₁

silly₂' : (n m : ℕ) →
         (n , n) ≡ (m , m) →
         ((q r : ℕ) → (q , q) ≡ (r , r) → q ∷ [] ≡ r ∷ []) →
         n ∷ [] ≡ m ∷ []
silly₂' n m eq₁ eq₂ = eq₂ n m eq₁

silly-ex : (p : ℕ) →
           ((n : ℕ) → even n ≡ true → even (suc n) ≡ false) →
           ((n : ℕ) → even n ≡ false → odd n ≡ true) →
           even p ≡ true →
           odd (suc p) ≡ true
silly-ex p H₁ H₂ H₃ = H₂ (suc p) (H₁ p H₃)

silly₃ : (n m : ℕ) → n ≡ m → m ≡ n
silly₃ n m eq₁ = sym eq₁

rev-exercise₁ : (l₁ l₂ : List ℕ) →
                l₁ ≡ rev l₂ →
                l₂ ≡ rev l₁
rev-exercise₁ l₁ l₂ eq rewrite eq = sym (rev-involutive l₂)

trans-eq-example₁ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₁ a b c d e f eq₁ eq₂ rewrite eq₁ | eq₂ = refl

trans-eq : {A : Set} → (n m o : A) →
           n ≡ m →
           m ≡ o →
           n ≡ o
trans-eq n m o eq₁ eq₂ rewrite eq₁ | eq₂ = refl

trans-eq' : {A : Set} → (n m o : A) →
            n ≡ m →
            m ≡ o →
            n ≡ o
trans-eq' n m o eq₁ eq₂ = begin
  n ≡⟨ eq₁ ⟩
  m ≡⟨ eq₂ ⟩
  o ∎

trans-eq-example₂ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₂ a b c d e f eq₁ eq₂ =
  trans-eq (a ∷ b ∷ []) (c ∷ d ∷ []) (e ∷ f ∷ []) eq₁ eq₂


trans-eq-example₃ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₃ a b c d e f eq₁ eq₂ = begin
  a ∷ b ∷ [] ≡⟨ eq₁ ⟩
  c ∷ d ∷ [] ≡⟨ eq₂ ⟩
  e ∷ f ∷ [] ∎

trans-eq-example₄ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₄ a b c d e f eq₁ eq₂ = trans eq₁ eq₂

trans-eq-example₅ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₅ a b c d e f refl refl = refl

trans-eq-exercise : (n m o p : ℕ) →
                    m ≡ minustwo o →
                    n + p ≡ m →
                    n + p ≡ minustwo o
trans-eq-exercise n m o p eq₁ eq₂ = trans eq₂ eq₁

trans-eq-exercise' : (n m o p : ℕ) →
                     m ≡ minustwo o →
                     n + p ≡ m →
                     n + p ≡ minustwo o
trans-eq-exercise' n m o p refl eq₂ = eq₂

suc-injective : {n m : ℕ} →
                suc n ≡ suc m →
                n ≡ m
suc-injective {n} {m} eq₁ = cong pred eq₁

injection-ex₁ : (n m o : ℕ) →
                n ∷ m ∷ [] ≡ o ∷ o ∷ [] →
                n ≡ m
injection-ex₁ n m o refl = refl

injection-ex₃ : {A : Set} → (x y z : A) → (l j : List A) →
                x ∷ y ∷ l ≡ z ∷ j →
                j ≡ z ∷ l →
                x ≡ y
injection-ex₃ x y z l j refl refl = refl

discriminate-ex₁ : (n m : ℕ) → false ≡ true → n ≡ m
discriminate-ex₁ n m ()

discriminate-ex₂ : (n : ℕ) → suc n ≡ zero → 2 + 2 ≡ 5
discriminate-ex₂ n ()

discriminate-ex₃ : {A : Set} → (x y z : A) → (l j : List A) →
                   x ∷ y ∷ l ≡ [] →
                   x ≡ z
discriminate-ex₃ x y z l j ()

eqb-0-l : (n : ℕ) → (0 =? n) ≡ true → n ≡ 0
eqb-0-l zero eq = refl

f-equal : {A B : Set} → (f : A → B) → (x y : A) →
          x ≡ y →
          f x ≡ f y
f-equal f x y refl = refl

eq-implies-suc-eq : (n m : ℕ) → n ≡ m → suc n ≡ suc m
eq-implies-suc-eq = f-equal suc

suc-inj : (n m : ℕ) → (b : Bool) →
          suc n =? suc m ≡ b →
          n =? m ≡ b
suc-inj n m b refl = refl

silly₄ : (n m p q : ℕ) →
         (n ≡ m → p ≡ q) →
         m ≡ n →
         q ≡ p
silly₄ n m p q eq₁ eq₂ = sym (eq₁ (sym eq₂))

silly₄' : (n m p q : ℕ) →
          (n ≡ m → p ≡ q) →
          m ≡ n →
          q ≡ p
silly₄' n m p q eq refl = sym (eq refl)

specialize-example : (n : ℕ) → ((m : ℕ) → m * n ≡ 0) → n ≡ 0
specialize-example n eq = trans one-times-n (eq 1)
  where
    one-times-n : n ≡ 1 * n
    one-times-n = sym (mult-1-l n)

trans-eq-example₆ : (a b c d e f : ℕ) →
                    a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                    c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                    a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example₆ a b c d e f eq₁ eq₂ = apply-to-endpoints eq₁ eq₂
  where
    trans-via-cd : (n o : List ℕ) → n ≡ c ∷ d ∷ [] → c ∷ d ∷ [] ≡ o → n ≡ o
    trans-via-cd n o = trans-eq n (c ∷ d ∷ []) o

    apply-to-endpoints : a ∷ b ∷ [] ≡ c ∷ d ∷ [] →
                         c ∷ d ∷ [] ≡ e ∷ f ∷ [] →
                         a ∷ b ∷ [] ≡ e ∷ f ∷ []
    apply-to-endpoints = trans-via-cd (a ∷ b ∷ []) (e ∷ f ∷ [])

double-injective : (n m : ℕ) →
                   double n ≡ double m →
                   n ≡ m
double-injective zero zero eq = refl
double-injective (suc n) (suc m) eq = f-equal suc n m ihn
  where
    double-eq : double n ≡ double m
    double-eq = suc-injective (suc-injective eq)

    ihn : n ≡ m
    ihn = double-injective n m double-eq

eqb-true : (n m : ℕ) →
           n =? m ≡ true →
           n ≡ m
eqb-true zero zero eq = refl
eqb-true (suc n) (suc m) eq = f-equal suc n m (eqb-true n m eq)

plus-n-n-injective : (n m : ℕ) →
                     n + n ≡ m + m →
                     n ≡ m
plus-n-n-injective zero zero eq = refl
plus-n-n-injective (suc n) (suc m) eq = f-equal suc n m ihn
  where
    normalized-eq : suc (n + n) ≡ suc (m + m)
    normalized-eq rewrite (plus-n-suc-m n n) | (plus-n-suc-m m m) = suc-injective eq

    doubles-eq : n + n ≡ m + m
    doubles-eq = suc-injective normalized-eq

    ihn : n ≡ m
    ihn = plus-n-n-injective n m doubles-eq

nth-error-after-last : {A : Set} → (n : ℕ) → (l : List A) →
                       length l ≡ n →
                       nth-error l n ≡ nothing
nth-error-after-last n [] eq = refl
nth-error-after-last (suc n) (x ∷ xs) refl = nth-error-after-last n xs refl
