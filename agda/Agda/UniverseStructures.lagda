This is modified from TarskiUniverseHierarchies.lagda

Instead of trying to define / construct a universe hierarchy by some
form of induction-recursion, we specify what a universe hierarchy is /
can be.

\begin{code}

{-# OPTIONS --without-K #-}

module UniverseStructures where

open import MLTT

\end{code}

We specify two universe hierarchies,

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


record cumulative-by-coercion (𝓛 : Succ-Sup-Semilattice) : Set₁ where
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

  T-⌜ℕ₀⌝ : (i   : L)                             → T i (⌜ℕ₀⌝ i)            ≡₁ ℕ₀
  T-⌜ℕ₁⌝ : (i   : L)                             → T i (⌜ℕ₁⌝ i)            ≡₁ ℕ₁
  T-⌜ℕ⌝  : (i   : L)                             → T i (⌜ℕ⌝ i)             ≡₁ ℕ
  T-⌜+⌝  : (i j : L) (a : U i) (b : U j)         → T (i ∨ j) (⌜+⌝ i j a b) ≡₁ T i a + T j b
  T-⌜Π⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Π⌝ i j a b) ≡₁ Π (T i a) (λ x → T j (b x))
  T-⌜Σ⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Σ⌝ i j a b) ≡₁ Σ (T i a) (λ x → T j (b x))
  T-⌜W⌝  : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜W⌝ i j a b) ≡₁ W (T i a) (λ x → T j (b x))
  T-⌜Id⌝ : (i   : L) (a : U i) (x y : T i a)     → T i (⌜Id⌝ i a x y)      ≡₁ Id (T i a) x y
  T-⌜U⌝  : (i   : L)                             → T (i ⁺) (⌜U⌝ i)         ≡₁ U i


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

  T-⌜ℕ₀⌝   :                                         T O ⌜ℕ₀⌝                 ≡₁ ℕ₀
  T-⌜ℕ₁⌝   :                                         T O ⌜ℕ₁⌝                 ≡₁ ℕ₁
  T-⌜ℕ⌝    :                                         T O ⌜ℕ⌝                  ≡₁ ℕ
  T-⌜+⌝    : (i j : L) (a : U i) (b : U j)         → T (i ∨ j) (⌜+⌝ i j a b)  ≡₁ T i a + T j b
  T-⌜Π⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Π⌝ i j a b)  ≡₁ Π (T i a) (λ x → T j (b x))
  T-⌜Σ⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜Σ⌝ i j a b)  ≡₁ Σ (T i a) (λ x → T j (b x))
  T-⌜W⌝    : (i j : L) (a : U i) (b : T i a → U j) → T (i ∨ j) (⌜W⌝ i j a b)  ≡₁ W (T i a) (λ x → T j (b x))
  T-⌜Id⌝   : (i   : L) (a : U i) (x y : T i a)     → T i (⌜Id⌝ i a x y)       ≡₁ Id (T i a) x y
  T-⌜U⌝    : (i   : L)                             → T (i ⁺) (⌜U⌝ i)          ≡₁ U i
  T-⌜Lift⌝ : (i j : L) (a : U i)                   → T (i ∨ j) (⌜Lift⌝ i j a) ≡₁ T i a

\end{code}
