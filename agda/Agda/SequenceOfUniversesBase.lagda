An ℕ-indexed tower of universes within Palmgren's superuniverse.

\begin{code}

{-# OPTIONS --without-K #-}

module SequenceOfUniversesBase where

open import MLTT
open import Palmgren

\end{code}

We choose the first universe to be empty, but then we work only with v
(succ n).

\begin{code}

internal-universe : Set
internal-universe = Σ u ꞉ V , (S u → V)

\end{code}

From an internal universe (u , t) we get an external universe (U , T)
defined by U = Carrier (u , t) and T = Structure (u , t).

\begin{code}

Carrier : internal-universe → Set
Carrier (u , t) = S u

Structure : (i : internal-universe) → Carrier i → Set
Structure (u , t) a = S (t a)

next : internal-universe → internal-universe
next (u , t) = ⌜U⌝ u t , ⌜T⌝ u t

v : ℕ → internal-universe
v zero     = ⌜ℕ₀⌝ , ℕ₀-induction (λ _ → V)
v (succ x) = next (v x)

𝓥 : ℕ → Set
𝓥 n = Carrier (v (succ n))

𝓢 : (n : ℕ) → 𝓥 n → Set
𝓢 n = Structure (v (succ n))
\end{code}
