We carve universes à la Agda from a superuniverse à la Palmgren. But
some equalities we would like to be definitional are only
identifications (as expected).

\begin{code}

{-# OPTIONS --without-K #-}

open import MLTT
open import Palmgren
open import SequenceOfUniversesBase
open import Arithmetic

module SequenceOfUniversesV2 where

lift-succ : (n : ℕ) → 𝓥 n → 𝓥 (succ n)
lift-succ _ = successor.⌜T⌝

\end{code}

We want to define a lifting map 𝓥 m → 𝓥 (max m n). A direct induction
on m and n doesn't work. So we define it by reduction to an easily
defined lifting map 𝓥 m → 𝓥 (m ∔ k)

\begin{code}

lift-+  : (m k : ℕ) → 𝓥 m → 𝓥 (m ∔ k)
lift-+ m zero     a = a
lift-+ m (succ k) a = lift-succ (m ∔ k) (lift-+ m k a)

lift-≤ : (m n : ℕ) → m ≤ n → 𝓥 m → 𝓥 n
lift-≤ m n le a = b
 where
  k : ℕ
  k = n - m [ le ]

  p : m ∔ k ≡ n
  p = plus-comm m k ∙ minus-property n m le

  b : 𝓥 n
  b = transport 𝓥 p (lift-+ m k a)

lift-L-max : (m n : ℕ) → 𝓥 m → 𝓥 (max m n)
lift-L-max m n = lift-≤ m (max m n) (left-≤-max m n)

lift-R-max : (m n : ℕ) → 𝓥 n → 𝓥 (max m n)
lift-R-max m n = lift-≤ n (max m n) (right-≤-max m n)

\end{code}

We now need the following type coercions:

\begin{code}

𝓢-succ : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (lift-succ n a) → 𝓢 n a
𝓢-succ n a x = x

𝓢-+ : (m k : ℕ) (a : 𝓥 m) → 𝓢 (m ∔ k) (lift-+ m k a) → 𝓢 m a
𝓢-+ m zero     a x = x
𝓢-+ m (succ k) a x = 𝓢-+ m k a x

𝓢-≤ : (m n : ℕ) (le : m ≤ n) (a : 𝓥 m) → 𝓢 n (lift-≤ m n le a) → 𝓢 m a
𝓢-≤ m n le a x = z
 where
  k : ℕ
  k = n - m [ le ]

  p : m ∔ k ≡ n
  p = plus-comm m k ∙ minus-property n m le

  y : 𝓢 (m ∔ k) (lift-+ m k a)
  y = transportd⁻¹ ℕ 𝓥 𝓢 (lift-+ m k a) p x

  z : 𝓢 m a
  z = 𝓢-+ m k a y

𝓢-L-max : (m n : ℕ) (a : 𝓥 m) → 𝓢 (max m n) (lift-L-max m n a) → 𝓢 m a
𝓢-L-max m n = 𝓢-≤ m (max m n) (left-≤-max m n)

|ℕ₀| : (n : ℕ) → 𝓥 n
|ℕ₁| : (n : ℕ) → 𝓥 n
|ℕ|  : (n : ℕ) → 𝓥 n
|+|  : (m n : ℕ) → 𝓥 m → 𝓥 n → 𝓥 (max m n)
|Σ|  : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|Π|  : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|W|  : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
|Id| : (n : ℕ) → (a : 𝓥 n) → 𝓢 n a → 𝓢 n a → 𝓥 n
|U|  : (n : ℕ) → 𝓥 n
|T|  : (n : ℕ) → 𝓥 n → 𝓥 (succ n)

\end{code}

With this we can give the Agda universe structure to the Palmgren superuniverse:

\begin{code}

|ℕ₀| n       = successor.⌜ℕ₀⌝
|ℕ₁| n       = successor.⌜ℕ₁⌝
|ℕ|  n       = successor.⌜ℕ⌝
|+|  m n a b = successor._⌜+⌝_ (lift-L-max m n a) (lift-R-max m n b)
|Σ|  m n a b = successor.⌜Σ⌝   (lift-L-max m n a) (λ x → lift-R-max m n (b (𝓢-L-max m n a x)))
|Π|  m n a b = successor.⌜Π⌝   (lift-L-max m n a) (λ x → lift-R-max m n (b (𝓢-L-max m n a x)))
|W|  m n a b = successor.⌜W⌝   (lift-L-max m n a) (λ x → lift-R-max m n (b (𝓢-L-max m n a x)))
|Id| n       = successor.⌜Id⌝
|U|  n       = successor.⌜U⌝
|T|  n       = successor.⌜T⌝

\end{code}

The desired equations are the following:

\begin{code}

|ℕ₀|-eq : (n : ℕ) → 𝓢 n (|ℕ₀| n) ≡₁ ℕ₀
|ℕ₁|-eq : (n : ℕ) → 𝓢 n (|ℕ₁| n) ≡₁ ℕ₁
|ℕ|-eq  : (n : ℕ) → 𝓢 n (|ℕ| n) ≡₁ ℕ
|+|-eq  : (m n : ℕ) → (a : 𝓥 m) (b : 𝓥 n) → 𝓢 (max m n) (|+| m n a b) ≡₁ (𝓢 m a + 𝓢 n b)
|Σ|-eq  : (m n : ℕ) → (a : 𝓥 m) (b : 𝓢 m a → 𝓥 n) → 𝓢 (max m n) (|Σ| m n a b) ≡₁ (Σ x ꞉ 𝓢 m a , 𝓢 n (b x))
|Π|-eq  : (m n : ℕ) → (a : 𝓥 m) (b : 𝓢 m a → 𝓥 n) → 𝓢 (max m n) (|Π| m n a b) ≡₁ (Π x ꞉ 𝓢 m a , 𝓢 n (b x))
|W|-eq  : (m n : ℕ) → (a : 𝓥 m) (b : 𝓢 m a → 𝓥 n) → 𝓢 (max m n) (|W| m n a b) ≡₁ (W x ꞉ 𝓢 m a , 𝓢 n (b x))
|U|-eq : (n : ℕ) → 𝓢 (succ n) (|U| (succ n)) ≡₁ 𝓥 n
|T|-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (|T| n a) ≡₁ 𝓢 n a

\end{code}

Some of them hold definitionally, and the others require induction on ℕ.

\begin{code}

|ℕ₀|-eq n       = refl _
|ℕ₁|-eq n       = refl _
|ℕ|-eq  n       = refl _
|+|-eq  m n a b = {!!} -- > Messy.
|Σ|-eq  m n a b = {!!} --\
|Π|-eq  m n a b = {!!} -- > Even messier (lots of nested transports in a difficult-to-see induction on ℕ).
|W|-eq  m n a b = {!!} --/
|U|-eq  n       = refl _
|T|-eq  n a     = refl _

\end{code}

Here is some numerical evidence, for the moment:

\begin{code}

sample-|+|-eq  : (a : 𝓥 7)  (b : 𝓥 13)          → 𝓢 13 (|+| 7 13 a b) ≡₁ (𝓢 7 a + 𝓢 13 b)
sample-|Σ|-eq  : (a : 𝓥 7)  (b : 𝓢 7 a → 𝓥 13) → 𝓢 13 (|Σ| 7 13 a b) ≡₁ (Σ x ꞉ 𝓢 7 a , 𝓢 13 (b x))
sample-|Π|-eq  : (a : 𝓥 7)  (b : 𝓢 7 a → 𝓥 13) → 𝓢 13 (|Π| 7 13 a b) ≡₁ (Π x ꞉ 𝓢 7 a , 𝓢 13 (b x))
sample-|W|-eq  : (a : 𝓥 13) (b : 𝓢 13 a → 𝓥 7) → 𝓢 13 (|W| 13 7 a b) ≡₁ (W x ꞉ 𝓢 13 a , 𝓢 7 (b x))

sample-|+|-eq  a b = refl _
sample-|Σ|-eq  a b = refl _
sample-|Π|-eq  a b = refl _
sample-|W|-eq  a b = refl _

\end{code}

And it should be a meta-theorem that the desired equations hold
definitionally for any specific numeral, not just 7 and 13.
