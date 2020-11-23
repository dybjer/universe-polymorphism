This is based on work by Palmgren.

\begin{code}

{-# OPTIONS --without-K #-}

module Palmgren where

open import MLTT

\end{code}

A universe is just a pair (U , T) with

  * U : Set (the carrier), and
  * T : U → Set (the structure).

The following constructs an abstract universe (U' , T') from an
abstract universe (U , T), its successor.

\begin{code}

module successor (U : Set) (T : U -> Set) where

  data U' : Set
  T' : U' → Set

  data U' where
    ⌜ℕ₀⌝  : U'
    ⌜ℕ₁⌝  : U'
    ⌜ℕ⌝   : U'
    _⌜+⌝_ : U' → U' → U'
    ⌜Σ⌝   : (a : U') → (T' a → U') → U'
    ⌜Π⌝   : (a : U') → (T' a → U') → U'
    ⌜W⌝   : (a : U') → (T' a → U') → U'
    ⌜Id⌝  : (a : U') → T' a → T' a → U'
    ⌜U⌝   : U'
    ⌜T⌝   : U → U'

  T' ⌜ℕ₀⌝         = ℕ₀
  T' ⌜ℕ₁⌝         = ℕ₁
  T' ⌜ℕ⌝          = ℕ
  T' (a ⌜+⌝ b)    = T' a + T' b
  T' (⌜Σ⌝ a b)    = Σ (T' a) (λ x → T' (b x))
  T' (⌜Π⌝ a b)    = Π (T' a) (λ x → T' (b x))
  T' (⌜W⌝ a b)    = W (T' a) (λ x → T' (b x))
  T' (⌜Id⌝ a b c) = Id (T' a) b c
  T' ⌜U⌝          = U
  T' (⌜T⌝ a)      = T a

  carrier    = U'
  structure  = T'

\end{code}

The super-universe (V , S).

\begin{code}

data V : Set
S : V → Set

\end{code}

We also define (U , T) as follows, for the sake of readability of the
definition of (V , S).

We think of a pair (u , t), with u : V and t : S u → V, as an
"internal universe".

Then S u is a Set and λ (a : S u) → S (t a) is a family S u → Set, and
hence the pair (S u , λ (a : S u) → S (t a)) is the external version
of the internal universe (u , t). We define (U u t , T u t) to be the
successor universe of this external version.

\begin{code}

U : (u : V) (t : S u → V) → Set
T : (u : V) (t : S u → V) → U u t → Set

U u t = successor.carrier   (S u) (λ (a : S u) → S (t a))
T u t = successor.structure (S u) (λ (a : S u) → S (t a))

data V where
  ⌜ℕ₀⌝  : V
  ⌜ℕ₁⌝  : V
  ⌜ℕ⌝   : V
  _⌜+⌝_ : V → V → V
  ⌜Σ⌝   : (a : V) → (S a → V) → V
  ⌜Π⌝   : (a : V) → (S a → V) → V
  ⌜W⌝   : (a : V) → (S a → V) → V
  ⌜Id⌝  : (a : V) → S a → S a → V
  ⌜U⌝   : (u : V) → (S u → V) → V
  ⌜T⌝   : (u : V) (t : S u → V) → U u t → V

S ⌜ℕ₀⌝         = ℕ₀
S ⌜ℕ₁⌝         = ℕ₁
S ⌜ℕ⌝          = ℕ
S (a ⌜+⌝ b)    = S a + S b
S (⌜Σ⌝ a b)    = Σ (S a) (λ (x : S a) → S (b x))
S (⌜Π⌝ a b)    = Π (S a) (λ (x : S a) → S (b x))
S (⌜W⌝ a b)    = W (S a) (λ (x : S a) → S (b x))
S (⌜Id⌝ a x y) = Id (S a) x y
S (⌜U⌝ u t)    = U u t
S (⌜T⌝ u t a)  = T u t a

\end{code}
