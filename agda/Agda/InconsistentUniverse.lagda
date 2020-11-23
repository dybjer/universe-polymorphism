An inconsistent universe.

This file typechecks with --no-positivity-check and fails without it.

\begin{code}

{-# OPTIONS --without-K #-}
{-# OPTIONS --no-positivity-check #-}

module InconsistentUniverse where

open import MLTT

data Uᵢ : Set
Tᵢ : Uᵢ → Set

data Uᵢ where
 ⌜ℕ₀⌝   : Uᵢ
 ⌜ℕ₁⌝   : Uᵢ
 ⌜ℕ⌝    : Uᵢ
 ⌜+⌝    : Uᵢ → Uᵢ → Uᵢ
 ⌜Π⌝    : (a : Uᵢ) → (Tᵢ a → Uᵢ) → Uᵢ
 ⌜Σ⌝    : (a : Uᵢ) → (Tᵢ a → Uᵢ) → Uᵢ
 ⌜W⌝    : (a : Uᵢ) → (Tᵢ a → Uᵢ) → Uᵢ
 ⌜Id⌝   : (a : Uᵢ) → Tᵢ a → Tᵢ a → Uᵢ
 ⌜U⌝    : Uᵢ
 ⌜Lift⌝ : Uᵢ → Uᵢ

Tᵢ ⌜ℕ₀⌝         = ℕ₀
Tᵢ ⌜ℕ₁⌝         = ℕ₁
Tᵢ ⌜ℕ⌝          = ℕ
Tᵢ (⌜+⌝ a b)    = Tᵢ a + Tᵢ b
Tᵢ (⌜Π⌝ a b)    = Π (Tᵢ a) (λ x → Tᵢ (b x))
Tᵢ (⌜Σ⌝ a b)    = Σ (Tᵢ a) (λ x → Tᵢ (b x))
Tᵢ (⌜W⌝ a b)    = W (Tᵢ a) (λ x → Tᵢ (b x))
Tᵢ (⌜Id⌝ a x y) = Id (Tᵢ a) x y
Tᵢ ⌜U⌝          = Uᵢ
Tᵢ (⌜Lift⌝ a)   = Tᵢ a

\end{code}
