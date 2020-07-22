This is modified from TarskiUniverseHierarchies.lagda

Instead of trying to define / construct a universe hierarchy by some
form of induction-recursion, we specify what a universe hierarchy is /
can be.

\begin{code}

{-# OPTIONS --without-K #-}

module UniverseStructure where

open import Agda.Primitive public

\end{code}

We first introduce notation for some standard MLTT basic types:

\begin{code}

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

\end{code}

And then for some standard MLTT type formers.

\begin{code}

data _+_ (A B : Set) : Set where
 inl : A → A + B
 inr : B → A + B

+-induction : (A B : Set) (P : A + B → Set)
            → ((a : A) → P (inl a)) → ((b : B) → P(inr b)) → (c : A + B) → P c
+-induction A B P f g (inl a) = f a
+-induction A B P f g (inr b) = g b

Π : (A : Set) → (A → Set) → Set
Π A B = (x : A) → B x

data Σ (A : Set) (B : A → Set) : Set where
 _,_ : (a : A) → B a → Σ A B

Σ-induction : (A : Set) (B : A → Set) (P : Σ A B → Set)
            → ((a : A) → (b : B a) → P(a , b))
            → (c : Σ A B) → P c
Σ-induction A B P f (x , y) = f x y

data W (A : Set) (B : A → Set) : Set where
 sup : (a : A) → (B a → W A B) → W A B

W-induction : (A : Set) (B : A → Set) (P : W A B → Set)
            → ((a : A) → (s : B a → W A B) → ((b : B a) → P(s b)) → P(sup a s))
            → (w : W A B) → P w
W-induction A B P f (sup a s) = f a s (λ (b : B a) → W-induction A B P f (s b))

data Id (A : Set) : A → A → Set where
 refl : (a : A) → Id A a a

Id-induction : (A : Set) (P : (x y : A) → Id A x y → Set)
             → ((x : A) → P x x (refl x))
             → (a b : A) → (r : Id A a b) → P a b r
Id-induction A P f a a (refl a) = f a

_≡_ : {X : Set} → X → X → Set
x ≡ y = Id _ x y

infix 10 _≡_

\end{code}

Equality of sets:

\begin{code}

data _≣_ : Set → Set → Set₁ where
 refl : (A : Set) → A ≣ A

infix 10 _≣_

\end{code}

We specify two universe hierarchies:

 * cumulative by coercion, and

 * cumulative on the nose

both indexed by a succ-sup-semilattice L.

\begin{code}

record Succ-Sup-Semilattice : Set₁ where
 constructor
  succ-sup-semilattice

 field
  L   : Set
  O   : L
  _⁺  : L → L
  _∨_ : L → L → L

  bottom : (i : L)     → O ∨ i ≡ i
  idemp  : (i : L)     → i ∨ i ≡ i
  comm   : (i j : L)   → i ∨ j ≡ j ∨ i
  assoc  : (i j k : L) → i ∨ (j ∨ k) ≡ (i ∨ j) ∨ k
  distr  : (i j : L)   → (i ∨ j)⁺ ≡ (i ⁺) ∨ (j ⁺)

 _≤_ : L → L → Set
 x ≤ y = x ∨ y ≡ y

record cumulative-by-coersion (𝓛 : Succ-Sup-Semilattice) : Set₁ where
 open Succ-Sup-Semilattice 𝓛
 field
  U : L → Set
  T : (i : L) → U i → Set

  ⌜ℕ₀⌝  : (i : L) → U i
  ⌜ℕ₁⌝  : (i : L) → U i
  ⌜ℕ⌝   : (i : L) → U i
  ⌜+⌝   : (i j : L) → U i → U j → U (i ∨ j)
  ⌜Π⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜Σ⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜W⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜Id⌝  : (i : L) (a : U i) → T i a → T i a → U i
  ⌜U⌝   : (i : L) → U (i ⁺)

  T-⌜ℕ₀⌝ : (i   : L)                             → T i (⌜ℕ₀⌝ i)            ≣ ℕ₀
  T-⌜ℕ₁⌝ : (i   : L)                             → T i (⌜ℕ₁⌝ i)            ≣ ℕ₁
  T-⌜ℕ⌝  : (i   : L)                             → T i (⌜ℕ⌝ i)             ≣ ℕ
  T-⌜+⌝  : (i j : L) (a : U i) (b : U j)         → T (i ∨ j) (⌜+⌝ i j a b) ≣ T i a + T j b
  T-⌜Π⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Π⌝ i j a b) ≣ Π (T i a) (λ x → T j (b x))
  T-⌜Σ⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Σ⌝ i j a b) ≣ Σ (T i a) (λ x → T j (b x))
  T-⌜W⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜W⌝ i j a b) ≣ W (T i a) (λ x → T j (b x))
  T-⌜Id⌝ : (i   : L) (a : U i) (x y : T i a)     → T i (⌜Id⌝ i a x y)      ≣ Id (T i a) x y
  T-⌜U⌝  : (i   : L)                             → T (i ⁺) (⌜U⌝ i)         ≣ U i

record cumulative-on-the-nose (𝓛 : Succ-Sup-Semilattice) : Set₁ where
 open Succ-Sup-Semilattice 𝓛
 field
  U : L → Set
  T : (i : L) → U i → Set

  ⌜ℕ₀⌝   : U O
  ⌜ℕ₁⌝   : U O
  ⌜ℕ⌝    : U O
  ⌜+⌝    : (i j : L) → U i → U j → U (i ∨ j)
  ⌜Π⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜Σ⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜W⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ∨ j)
  ⌜Id⌝   : (i : L) (a : U i) → T i a → T i a → U i
  ⌜U⌝    : (i : L) → U (i ⁺)
  ⌜Lift⌝ : (i j : L) → U i → U (i ∨ j)

  T-⌜ℕ₀⌝   :                                         T O ⌜ℕ₀⌝                 ≣ ℕ₀
  T-⌜ℕ₁⌝   :                                         T O ⌜ℕ₁⌝                 ≣ ℕ₁
  T-⌜ℕ⌝    :                                         T O ⌜ℕ⌝                  ≣ ℕ
  T-⌜+⌝    : (i j : L) (a : U i) (b : U j)         → T (i ∨ j) (⌜+⌝ i j a b)  ≣ T i a + T j b
  T-⌜Π⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Π⌝ i j a b)  ≣ Π (T i a) (λ x → T j (b x))
  T-⌜Σ⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Σ⌝ i j a b)  ≣ Σ (T i a) (λ x → T j (b x))
  T-⌜W⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜W⌝ i j a b)  ≣ W (T i a) (λ x → T j (b x))
  T-⌜Id⌝   : (i   : L) (a : U i) (x y : T i a)     → T i (⌜Id⌝ i a x y)       ≣ Id (T i a) x y
  T-⌜U⌝    : (i   : L)                             → T (i ⁺) (⌜U⌝ i)          ≣ U i
  T-⌜Lift⌝ : (i j : L) (a : U i)                   → T (i ∨ j) (⌜Lift⌝ i j a) ≣ T i a

\end{code}
