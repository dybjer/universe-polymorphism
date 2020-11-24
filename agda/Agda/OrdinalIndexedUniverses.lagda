\begin{code}

{-# OPTIONS --without-K #-}

module OrdinalIndexedUniverses where

open import MLTT
open import SuperUniverse
open import SequenceOfUniversesBase

sum : (I : V) → (S I → internal-universe) → internal-universe
sum I α = (⌜Σ⌝ I (λ u → pr₁ (α u)) , λ {(u , s) → pr₂ (α u) s})

data Ord : Set where
 zero : Ord
 succ : Ord → Ord
 sup  : (ℕ → Ord) → Ord

w : Ord → internal-universe
w zero     = ⌜ℕ₀⌝ , λ ()
w (succ x) = next (w x)
w (sup α)  = sum ⌜ℕ⌝ (λ i → w (α i))

\end{code}
