An ℕ-indexed tower of universes within Palmgren's superuniverse.

\begin{code}

{-# OPTIONS --without-K #-}

module SequenceOfUniversesV1 where

open import MLTT
open import SuperUniverse
open import SequenceOfUniversesBase

module _ (n : ℕ) where

  |ℕ₀|   : 𝓥 n
  |ℕ₁|   : 𝓥 n
  |ℕ|    : 𝓥 n
  _|+|_  : 𝓥 n → 𝓥 n → 𝓥 n
  |Σ|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
  |Π|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
  |W|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
  |Id|   : (a : 𝓥 n) → 𝓢 n a → 𝓢 n a → 𝓥 n
  |U|    : 𝓥 n
  |T|    : 𝓥 n → 𝓥 (succ n)

  |ℕ₀|   = successor.⌜ℕ₀⌝
  |ℕ₁|   = successor.⌜ℕ₁⌝
  |ℕ|    = successor.⌜ℕ⌝
  _|+|_  = successor._⌜+⌝_
  |Σ|    = successor.⌜Σ⌝
  |Π|    = successor.⌜Π⌝
  |W|    = successor.⌜W⌝
  |Id|   = successor.⌜Id⌝
  |U|    = successor.⌜U⌝
  |T|    = successor.⌜T⌝

\end{code}

The equations that should hold definitionally indeed do:

\begin{code}

  |ℕ₀|-eq : 𝓢 n |ℕ₀| ≡₁ ℕ₀
  |ℕ₁|-eq : 𝓢 n |ℕ₁| ≡₁ ℕ₁
  |ℕ|-eq  : 𝓢 n |ℕ|  ≡₁ ℕ
  |+|-eq  : (a b : 𝓥 n) → 𝓢 n (a |+| b) ≡₁ (𝓢 n a + 𝓢 n b)
  |Σ|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Σ| a b) ≡₁ (Σ x ꞉ 𝓢 n a , 𝓢 n (b x))
  |Π|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Π| a b) ≡₁ (Π x ꞉ 𝓢 n a , 𝓢 n (b x))
  |W|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|W| a b) ≡₁ (W x ꞉ 𝓢 n a , 𝓢 n (b x))

  |ℕ₀|-eq    = refl _
  |ℕ₁|-eq    = refl _
  |ℕ|-eq     = refl _
  |+|-eq a b = refl _
  |Σ|-eq a b = refl _
  |Π|-eq a b = refl _
  |W|-eq a b = refl _

\end{code}

These equations need to go outside the above anonymous module, as they
using varying n's:

\begin{code}

|U|-eq : (n : ℕ) → 𝓢 (succ n) (|U| (succ n)) ≡₁ 𝓥 n
|T|-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (|T| n a) ≡₁ 𝓢 n a

|U|-eq n   = refl _
|T|-eq n a = refl _

\end{code}
