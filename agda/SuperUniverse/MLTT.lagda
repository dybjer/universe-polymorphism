\begin{code}

{-# OPTIONS --without-K #-}

module MLTT where

open import Agda.Primitive public

Type  = Set₀
Type₁ = Set₁

data ℕ₀ : Type where

ℕ₀-induction : (P : ℕ₀ → Type) → (n : ℕ₀) → P n
ℕ₀-induction P ()

data  ℕ₁ : Type where
 * :  ℕ₁

ℕ₁-induction : (P :  ℕ₁ → Type) → P * → (n : ℕ₁) → P n
ℕ₁-induction P x * = x

data ℕ : Type where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (P : ℕ → Type) → P zero → ((n : ℕ) → P n → P(succ n)) → (n : ℕ) → P n
ℕ-induction P x f zero = x
ℕ-induction P x f (succ n) = f n (ℕ-induction P x f n)

infixl 10 _+_
data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B

+-induction : (A B : Type) (P : A + B → Type)
            → ((a : A) → P (inl a)) → ((b : B) → P(inr b)) → (c : A + B) → P c
+-induction A B P f g (inl a) = f a
+-induction A B P f g (inr b) = g b

Π : (A : Type) → (A → Type) → Type
Π A B = (x : A) → B x

syntax Π X (λ x → y) = Π x ꞉ X , y

record Σ (A : Type) (B : A → Type) : Type where
 constructor
   _,_
 field
   pr₁ : A
   pr₂ : B pr₁

open Σ public

syntax Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : (A : Type) (B : A → Type) (P : Σ A B → Type)
            → ((a : A) → (b : B a) → P(a , b))
            → (c : Σ A B) → P c
Σ-induction A B P f (x , y) = f x y

data W (A : Type) (B : A → Type) : Type where
 sup : (a : A) → (B a → W A B) → W A B

syntax W X (λ x → y) = W x ꞉ X , y

W-induction : (A : Type) (B : A → Type) (P : W A B → Type)
            → ((a : A) → (s : B a → W A B) → ((b : B a) → P(s b)) → P(sup a s))
            → (w : W A B) → P w
W-induction A B P f (sup a s) = f a s (λ (b : B a) → W-induction A B P f (s b))

data Id (A : Type) : A → A → Type where
 refl : (a : A) → Id A a a

infix 0 _≡_
_≡_ : {A : Type} → A → A → Type
x ≡ y = Id _ x y

Id-induction : (A : Type) (P : (x y : A) → Id A x y → Type)
             → ((x : A) → P x x (refl x))
             → (a b : A) → (r : Id A a b) → P a b r
Id-induction A P f a a (refl a) = f a

_∙_ : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ refl _ = p

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl _) = refl _

transport : {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) → B x → B y
transport B (refl _) b = b

apd : {A : Type} {B : A → Type} (f : (x : A) → B x) {x y : A} (p : x ≡ y)
    → transport B p (f x) ≡ f y
apd p (refl _) = refl _

transportd : (A  : Type)
             (B  : A → Type)
             (C  : (x : A) → B x → Type)
             {x  : A}
             (y  : B x)
             {x' : A}
             (p : x ≡ x')
           → C x y → C x' (transport B p y)

transportd A B C y (refl _) z = z

transportd₁ : (A  : Type)
              (B  : A → Type)
              (C  : (x : A) → B x → Type₁)
              {x  : A}
              (y  : B x)
              {x' : A}
              (p : x ≡ x')
            → C x y → C x' (transport B p y)

transportd₁ A B C y (refl _) z = z

\end{code}

We also need to compare sets for equality:

\begin{code}

infix 0 _≡₁_
data _≡₁_ {A : Type₁} : A → A → Type₁ where
  refl : (a : A) → a ≡₁ a

transport₁ : {A : Type₁} (B : A → Type₁) {x y : A} (p : x ≡₁ y) → B x → B y
transport₁ B (refl _) b = b

Id-to-fun : {A B : Type} → A ≡₁ B → A → B
Id-to-fun (refl _) a = a

change-of-variable' : (ϕ    : (A  : Type) → (A → Type) → Type)
                      (A A' : Type)
                      (B    : A' → Type)
                      (p    : A ≡₁ A')

                    → ϕ A (λ x → B (Id-to-fun p x)) ≡₁ ϕ A' B

change-of-variable' ϕ A .A B (refl .A) = refl (ϕ A B)

\end{code}

(We will consider ϕ = Σ and ϕ = Π and ϕ = W in our applications.)

We need the following version of change of variable, which assumes the
extensionality of ϕ:

\begin{code}

is-extensional : ((A  : Type) → (A → Type) → Type) → Type₁
is-extensional ϕ = (A : Type)
                   (B B' : A → Type)
                 → ((x : A) → B x ≡₁ B' x)
                 → ϕ A B ≡₁ ϕ A B'

change-of-variable : (ϕ    : (A  : Type) → (A → Type) → Type)
                     (A A' : Type)
                     (B    : A → Type)
                     (B'   : A' → Type)
                     (p    : A ≡₁ A')
                     (q    : (x : A) → B x ≡₁ B' (Id-to-fun p x))

                   → is-extensional ϕ
                   → ϕ A B ≡₁ ϕ A' B'

change-of-variable ϕ A .A B B' (refl .A) q i = i A B B' q

\end{code}
