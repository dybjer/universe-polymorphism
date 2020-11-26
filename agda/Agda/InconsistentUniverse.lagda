An inconsistent universe.

This file typechecks with --no-positivity-check and fails without it.

\begin{code}

{-# OPTIONS --without-K #-}
{-# OPTIONS --no-positivity-check #-}

module InconsistentUniverse where

open import MLTT

data U : Set
T : U → Set

data U where
 ⌜ℕ₀⌝ : U
 ⌜ℕ₁⌝ : U
 ⌜ℕ⌝  : U
 ⌜+⌝  : U → U → U
 ⌜Π⌝  : (a : U) → (T a → U) → U
 ⌜Σ⌝  : (a : U) → (T a → U) → U
 ⌜W⌝  : (a : U) → (T a → U) → U
 ⌜Id⌝ : (a : U) → T a → T a → U
 ⌜U⌝  : U

T ⌜ℕ₀⌝         = ℕ₀
T ⌜ℕ₁⌝         = ℕ₁
T ⌜ℕ⌝          = ℕ
T (⌜+⌝ a b)    = T a + T b
T (⌜Π⌝ a b)    = Π (T a) (λ x → T (b x))
T (⌜Σ⌝ a b)    = Σ (T a) (λ x → T (b x))
T (⌜W⌝ a b)    = W (T a) (λ x → T (b x))
T (⌜Id⌝ a x y) = Id (T a) x y
T ⌜U⌝          = U

\end{code}
