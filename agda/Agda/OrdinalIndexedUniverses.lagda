Peter Dybjer defines, in the Agda wiki, "the first universe à la
Tarski" by induction-recursion:

http://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.RulesForTheStandardSetFormers

Here we define two hierarchies of universes à la Tarski, indexed by a
successor-sup-semilattice, one cumulative by coercion, and the other
cumulative on the nose.

The Agda type Set (or Set₀) will host all these universes à la Tarski.

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

I think that now we will lose some definitional equalities, compared
to the ℕ-indexed tower. Leave this for later.
