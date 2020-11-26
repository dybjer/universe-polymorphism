We carve universes à la Agda from a superuniverse à la Palmgren. But
some equalities we would like to be definitional are only
identifications, as expected, and moreover seem to require some amount
of extensionality, which may be unexpected, for the cases of Σ, Π and W.

\begin{code}

{-# OPTIONS --without-K #-}

open import MLTT
open import SuperUniverse
open import SequenceOfUniversesBase
open import Arithmetic

module SequenceOfUniverses-a-la-Agda where

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

𝓢-succ-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (lift-succ n a) ≡₁ 𝓢 n a
𝓢-succ-eq n a = refl _

𝓢-+-eq : (m k : ℕ) (a : 𝓥 m) → 𝓢 (m ∔ k) (lift-+ m k a) ≡₁ 𝓢 m a
𝓢-+-eq m zero     a = refl _
𝓢-+-eq m (succ k) a = 𝓢-+-eq m k a

𝓢-≤-eq : (m n : ℕ) (le : m ≤ n) (a : 𝓥 m) → 𝓢 n (lift-≤ m n le a) ≡₁ 𝓢 m a
𝓢-≤-eq m n le a = r
 where
  k : ℕ
  k = n - m [ le ]

  p : m ∔ k ≡ n
  p = plus-comm m k ∙ minus-property n m le

  q : 𝓢 (m ∔ k) (lift-+ m k a) ≡₁ 𝓢 m a
  q = 𝓢-+-eq m k a

  r : 𝓢 n (lift-≤ m n le a) ≡₁ 𝓢 m a
  r = transportd₁ ℕ 𝓥 (λ l b → 𝓢 l b ≡₁ 𝓢 m a) (lift-+ m k a) p q

𝓢-L-max-eq : (m n : ℕ) (a : 𝓥 m) → 𝓢 (max m n) (lift-L-max m n a) ≡₁ 𝓢 m a
𝓢-L-max-eq m n = 𝓢-≤-eq m (max m n) (left-≤-max m n)

𝓢-R-max-eq : (m n : ℕ) (b : 𝓥 n) → 𝓢 (max m n) (lift-R-max m n b) ≡₁ 𝓢 n b
𝓢-R-max-eq m n = 𝓢-≤-eq n (max m n) (right-≤-max m n)

\end{code}

We also need the following type coercion:

\begin{code}

𝓢-L-max : (m n : ℕ) (a : 𝓥 m) → 𝓢 (max m n) (lift-L-max m n a) → 𝓢 m a
𝓢-L-max m n a = Id-to-fun (𝓢-L-max-eq m n a)

\end{code}

With this we can give the Agda universe structure to the Palmgren superuniverse:

\begin{code}

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

To prove the desired equations, we seem to need some amount of
extensionality, which we assume in the following anonymous module.

\begin{code}

module _ (Σ-ext : is-extensional Σ)
         (Π-ext : is-extensional Π)
         (W-ext : is-extensional W)
       where

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

Some of them hold definitionally, but the others don't. Moreover, as
alluded above, they seem to require extensionality, which would be
removable if we replaced type equality ≡₁ by type equivalence ≃ in the
above equations.

\begin{code}

  |ℕ₀|-eq n       = refl _
  |ℕ₁|-eq n       = refl _
  |ℕ|-eq  n       = refl _
  |+|-eq  m n a b = t
   where
    p : 𝓢 (max m n) (|+| m n a b) ≡₁ 𝓢 (max m n) (lift-L-max m n a) + 𝓢 (max m n) (lift-R-max m n b)
    p = refl _
    r : 𝓢 (max m n) (lift-L-max m n a) ≡₁ 𝓢 m a
    r = 𝓢-L-max-eq m n a
    s : 𝓢 (max m n) (lift-R-max m n b) ≡₁ 𝓢 n b
    s = 𝓢-R-max-eq m n b
    t : 𝓢 (max m n) (|+| m n a b) ≡₁ 𝓢 m a + 𝓢 n b
    t = transport₁ (λ - → 𝓢 (max m n) (|+| m n a b) ≡₁ 𝓢 m a + -) s
         (transport₁ (λ - → 𝓢 (max m n) (|+| m n a b) ≡₁ - + 𝓢 (max m n) (lift-R-max m n b)) r p)
  |Σ|-eq  m n a b = t
   where
    A : Set
    A = 𝓢 (max m n) (lift-L-max m n a)
    B : A → Set
    B x = 𝓢 (max m n) (lift-R-max m n (b (𝓢-L-max m n a x)))
    p : 𝓢 (max m n) (|Σ| m n a b) ≡₁ Σ x ꞉ A , B x
    p = refl _
    r : A ≡₁ 𝓢 m a
    r = 𝓢-L-max-eq m n a
    s : (x : A) → B x ≡₁ 𝓢 n (b (𝓢-L-max m n a x))
    s x = 𝓢-R-max-eq m n (b (𝓢-L-max m n a x))
    t : 𝓢 (max m n) (|Σ| m n a b) ≡₁ Σ y ꞉ 𝓢 m a , 𝓢 n (b y)
    t = change-of-variable Σ A (𝓢 m a) B (λ x → 𝓢 n (b x)) r s Σ-ext
  |Π|-eq  m n a b = t
   where
    A : Set
    A = 𝓢 (max m n) (lift-L-max m n a)
    B : A → Set
    B x = 𝓢 (max m n) (lift-R-max m n (b (𝓢-L-max m n a x)))
    p : 𝓢 (max m n) (|Π| m n a b) ≡₁ Π x ꞉ A , B x
    p = refl _
    r : A ≡₁ 𝓢 m a
    r = 𝓢-L-max-eq m n a
    s : (x : A) → B x ≡₁ 𝓢 n (b (𝓢-L-max m n a x))
    s x = 𝓢-R-max-eq m n (b (𝓢-L-max m n a x))
    t : 𝓢 (max m n) (|Π| m n a b) ≡₁ Π x ꞉ 𝓢 m a , 𝓢 n (b x)
    t = change-of-variable Π A (𝓢 m a) B (λ x → 𝓢 n (b x)) r s Π-ext
  |W|-eq  m n a b = t
   where
    A : Set
    A = 𝓢 (max m n) (lift-L-max m n a)
    B : A → Set
    B x = 𝓢 (max m n) (lift-R-max m n (b (𝓢-L-max m n a x)))
    p : 𝓢 (max m n) (|W| m n a b) ≡₁ W x ꞉ A , B x
    p = refl _
    r : A ≡₁ 𝓢 m a
    r = 𝓢-L-max-eq m n a
    s : (x : A) → B x ≡₁ 𝓢 n (b (𝓢-L-max m n a x))
    s x = 𝓢-R-max-eq m n (b (𝓢-L-max m n a x))
    t : 𝓢 (max m n) (|W| m n a b) ≡₁ W x ꞉ 𝓢 m a , 𝓢 n (b x)
    t = change-of-variable W A (𝓢 m a) B (λ x → 𝓢 n (b x)) r s W-ext

  |U|-eq  n       = refl _
  |T|-eq  n a     = refl _

\end{code}

(This is the end of the anonymous module.)

However, without extensionality, it should be a meta-theorem that the
desired equations hold definitionally for any numeral. We test this
conjecture with 7 and 13:

\begin{code}

sample-|+|-eq  : (a : 𝓥 7)  (b : 𝓥 13)         → 𝓢 13 (|+| 7 13 a b) ≡₁ (𝓢 7 a + 𝓢 13 b)
sample-|Σ|-eq  : (a : 𝓥 7)  (b : 𝓢 7 a → 𝓥 13) → 𝓢 13 (|Σ| 7 13 a b) ≡₁ (Σ x ꞉ 𝓢 7 a , 𝓢 13 (b x))
sample-|Π|-eq  : (a : 𝓥 7)  (b : 𝓢 7 a → 𝓥 13) → 𝓢 13 (|Π| 7 13 a b) ≡₁ (Π x ꞉ 𝓢 7 a , 𝓢 13 (b x))
sample-|W|-eq  : (a : 𝓥 13) (b : 𝓢 13 a → 𝓥 7) → 𝓢 13 (|W| 13 7 a b) ≡₁ (W x ꞉ 𝓢 13 a , 𝓢 7 (b x))

sample-|+|-eq  a b = refl _
sample-|Σ|-eq  a b = refl _
sample-|Π|-eq  a b = refl _
sample-|W|-eq  a b = refl _

\end{code}
