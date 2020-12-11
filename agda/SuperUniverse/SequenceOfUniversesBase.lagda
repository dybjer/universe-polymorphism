An ℕ-indexed tower of universes within Palmgren's superuniverse.

\begin{code}

{-# OPTIONS --without-K #-}

module SequenceOfUniversesBase where

open import MLTT
open import SuperUniverse

\end{code}

We choose the first universe v zero to be empty, but then we work only
with v (succ n).

\begin{code}

internal-universe : Type
internal-universe = Σ u ꞉ V , (S u → V)

\end{code}

From an internal universe (u , t) we get an external universe (U , T)
defined by U = Carrier (u , t) and T = Structure (u , t).

\begin{code}

Carrier : internal-universe → Type
Carrier (u , t) = S u

Structure : (i : internal-universe) → Carrier i → Type
Structure (u , t) a = S (t a)

next : internal-universe → internal-universe
next (u , t) = ⌜U⌝ u t , ⌜T⌝ u t

v : ℕ → internal-universe
v zero     = ⌜ℕ₀⌝ , ℕ₀-induction (λ _ → V)
v (succ x) = next (v x)

𝓥 : ℕ → Type
𝓥 n = Carrier (v (succ n))

𝓢 : (n : ℕ) → 𝓥 n → Type
𝓢 n = Structure (v (succ n))

\end{code}
