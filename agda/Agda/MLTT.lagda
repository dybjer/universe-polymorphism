\begin{code}

{-# OPTIONS --without-K #-}

module MLTT where

open import Agda.Primitive public

data ℕ₀ : Set where

ℕ₀-induction : (P : ℕ₀ → Set) → (n : ℕ₀) → P n
ℕ₀-induction P ()

data  ℕ₁ : Set where
 * :  ℕ₁

ℕ₁-induction : (P :  ℕ₁ → Set) → P * → (n : ℕ₁) → P n
ℕ₁-induction P x * = x

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

ℕ-induction : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P(succ n)) → (n : ℕ) → P n
ℕ-induction P x f zero = x
ℕ-induction P x f (succ n) = f n (ℕ-induction P x f n)

infixl 10 _+_
data _+_ (A B : Set) : Set where
 inl : A → A + B
 inr : B → A + B

+-induction : (A B : Set) (P : A + B → Set)
            → ((a : A) → P (inl a)) → ((b : B) → P(inr b)) → (c : A + B) → P c
+-induction A B P f g (inl a) = f a
+-induction A B P f g (inr b) = g b

Π : (A : Set) → (A → Set) → Set
Π A B = (x : A) → B x

syntax Π X (λ x → y) = Π x ꞉ X , y

record Σ (A : Set) (B : A → Set) : Set where
 constructor
   _,_
 field
   pr₁ : A
   pr₂ : B pr₁

open Σ public

syntax Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : (A : Set) (B : A → Set) (P : Σ A B → Set)
            → ((a : A) → (b : B a) → P(a , b))
            → (c : Σ A B) → P c
Σ-induction A B P f (x , y) = f x y

data W (A : Set) (B : A → Set) : Set where
 sup : (a : A) → (B a → W A B) → W A B

syntax W X (λ x → y) = W x ꞉ X , y

W-induction : (A : Set) (B : A → Set) (P : W A B → Set)
            → ((a : A) → (s : B a → W A B) → ((b : B a) → P(s b)) → P(sup a s))
            → (w : W A B) → P w
W-induction A B P f (sup a s) = f a s (λ (b : B a) → W-induction A B P f (s b))

data Id (A : Set) : A → A → Set where
 refl : (a : A) → Id A a a

infix 0 _≡_
_≡_ : {A : Set} → A → A → Set
x ≡ y = Id _ x y

Id-induction : (A : Set) (P : (x y : A) → Id A x y → Set)
             → ((x : A) → P x x (refl x))
             → (a b : A) → (r : Id A a b) → P a b r
Id-induction A P f a a (refl a) = f a

ap : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl _) = refl _

transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport B (refl _) b = b

infix 0 _≡₁_
data _≡₁_ {A : Set₁} : A → A → Set₁ where
  refl : (a : A) → a ≡₁ a

\end{code}

Some general functions and relations:

\begin{code}

infixl 10 _∔_
_∔_ : ℕ → ℕ → ℕ
x ∔ zero   = x
x ∔ succ y = succ (x ∔ y)

_≤_ : ℕ → ℕ → Set
zero   ≤ n      = ℕ₁
succ m ≤ zero   = ℕ₀
succ m ≤ succ n = m ≤ n

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero     = *
≤-refl (succ n) = ≤-refl n

_-_[_] : (m n : ℕ) → n ≤ m → ℕ
zero     - n        [ le ] = zero
(succ m) - zero     [ *  ] = succ m
(succ m) - (succ n) [ le ] = m - n [ le ]

minus-property : (m n : ℕ) (le : n ≤ m) → (m - n [ le ]) ∔ n ≡ m
minus-property zero     zero     *  = refl zero
minus-property (succ m) zero     *  = refl (succ m)
minus-property (succ m) (succ n) le = ap succ (minus-property m n le)

max : ℕ → ℕ → ℕ
max zero     n        = n
max (succ m) zero     = succ m
max (succ m) (succ n) = succ (max m n)

≤-max : (m n : ℕ) → m ≤ max m n
≤-max zero     n        = *
≤-max (succ m) zero     = ≤-refl m
≤-max (succ m) (succ n) = ≤-max m n

max-minus-property : (m n : ℕ) → (max m n - m [ ≤-max m n ]) ∔ m ≡ max m n
max-minus-property m n = minus-property (max m n) m (≤-max m n)

max-comm : (m n : ℕ) → max m n ≡ max n m
max-comm zero     zero     = refl zero
max-comm zero     (succ n) = refl (succ n)
max-comm (succ m) zero     = refl (succ m)
max-comm (succ m) (succ n) = ap succ (max-comm m n)

\end{code}
