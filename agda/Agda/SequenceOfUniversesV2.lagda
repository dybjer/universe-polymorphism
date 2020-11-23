We carve universes à la Agda from a superuniverse à la Palmgren. But
some equalities we would like to be definitional are only
identifications.

This module is incomplete.

\begin{code}

{-# OPTIONS --without-K #-}

open import MLTT
open import Palmgren
open import SequenceOfUniversesBase

module SequenceOfUniversesV2 where

Lift-succ : (n : ℕ) → 𝓥 n → 𝓥 (succ n)
Lift-succ _ = successor.⌜T⌝

𝓢-succ : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (Lift-succ n a) ≡₁ 𝓢 n a
𝓢-succ n a = refl _

𝓢-succ→ : (n : ℕ) (a : 𝓥 n) → 𝓢 n a → 𝓢 (succ n) (Lift-succ n a)
𝓢-succ→ n a x = x

𝓢-succ← : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (Lift-succ n a) → 𝓢 n a
𝓢-succ← n a x = x
Lift₀ : (n : ℕ) → 𝓥 zero → 𝓥 n
Lift₀ zero     a = a
Lift₀ (succ n) a = Lift-succ n (Lift₀ n a)

Lift-+  : (n k : ℕ) → 𝓥 n → 𝓥 (n ∔ k)
Lift-+ n zero     a = a
Lift-+ n (succ k) a = Lift-succ (n ∔ k) (Lift-+ n k a)


LiftR   : (m n : ℕ) → 𝓥 n → 𝓥 (max m n)
LiftR m n a = {!!}

Lift-L-max : (m n : ℕ) → 𝓥 m → 𝓥 (max m n)
Lift-L-max m n a = t (max m n - m [ ≤-max m n ] ∔ m) (max m n) (max-minus-property m n) b
 where
  t : (x y : ℕ) → Id ℕ x y → 𝓥 x → 𝓥 y
  t x x (refl x) a = a
  b : 𝓥 (max m n - m [ ≤-max m n ] ∔ m)
  b = Lift-+ m {!max m n - m [ ≤-max m n ]!} a
  -- Lift-+ m (max m n - m [ ≤-max m n ]) ?


Lift-L-max→ : (m n : ℕ) (a : 𝓥 m) → 𝓢 m a → 𝓢 (max m n) (Lift-L-max m n a)
Lift-L-max→ m n a x = {!!}

Lift-L-max← : (m n : ℕ) (a : 𝓥 m) → 𝓢 (max m n) (Lift-L-max m n a) → 𝓢 m a
Lift-L-max← m n a x = {!!}


Lift-R-max   : (m n : ℕ) → 𝓥 n → 𝓥 (max m n)
Lift-R-max zero     n a        = a
Lift-R-max (succ m) zero a     = Lift₀ (succ m) a
Lift-R-max (succ m) (succ n) a = {!!}


|ℕ₀|   : (n : ℕ) → 𝓥 n
|ℕ₁|   : (n : ℕ) → 𝓥 n
|ℕ|    : (n : ℕ) → 𝓥 n
_|+|_  : (m n : ℕ) → 𝓥 m → 𝓥 n → 𝓥 (max m n)
|Σ|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|Π|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|W|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|Id|   : (n : ℕ) → (a : 𝓥 n) → 𝓢 n a → 𝓢 n a → 𝓥 n
|U|    : (n : ℕ) → 𝓥 n
|T|    : (n : ℕ) → 𝓥 n → 𝓥 (succ n)

|ℕ₀|   n       = successor.⌜ℕ₀⌝
|ℕ₁|   n       = successor.⌜ℕ₁⌝
|ℕ|    n       = successor.⌜ℕ⌝
_|+|_  m n a b = successor._⌜+⌝_ (Lift-L-max m n a) (Lift-R-max m n b)
|Σ|    m n a b = successor.⌜Σ⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
|Π|    m n a b = successor.⌜Π⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
|W|    m n a b = successor.⌜W⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
|Id|   n       = successor.⌜Id⌝
|U|    n       = successor.⌜U⌝
|T|    n       = successor.⌜T⌝

{-
|ℕ₀|-eq : (n : ℕ) → 𝓢 n |ℕ₀| ≡₁ ℕ₀
|ℕ₁|-eq : (n : ℕ) → 𝓢 n |ℕ₁| ≡₁ ℕ₁
|ℕ|-eq  : (n : ℕ) → 𝓢 n |ℕ|  ≡₁ ℕ
|+|-eq  : (m n : ℕ) → (a b : 𝓥 n) → 𝓢 n (a |+| b) ≡₁ (𝓢 n a + 𝓢 n b)
|Σ|-eq  : (m n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Σ| a b) ≡₁ (Σ x ꞉ 𝓢 n a , 𝓢 n (b x))
|Π|-eq  : (m n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Π| a b) ≡₁ (Π x ꞉ 𝓢 n a , 𝓢 n (b x))
|W|-eq  : (n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|W| a b) ≡₁ (W x ꞉ 𝓢 n a , 𝓢 n (b x))
|U|-eq : (n : ℕ) → 𝓢 (succ n) (|U| (succ n)) ≡₁ 𝓥 n
|T|-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (|T| n a) ≡₁ 𝓢 n a

|ℕ₀|-eq    = refl _
|ℕ₁|-eq    = refl _
|ℕ|-eq     = refl _
|+|-eq a b = refl _
|Σ|-eq a b = refl _
|Π|-eq a b = refl _
|W|-eq a b = refl _
|U|-eq n   = refl _
|T|-eq n a = refl _
-}
\end{code}
