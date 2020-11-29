\begin{code}

{-# OPTIONS --without-K #-}

module Arithmetic where

open import MLTT

infixl 10 _∔_
_∔_ : ℕ → ℕ → ℕ
m ∔ zero   = m
m ∔ succ n = succ (m ∔ n)

zero-left : (m : ℕ) → zero ∔ m ≡ m
zero-left zero     = refl zero
zero-left (succ m) = ap succ (zero-left m)

succ-left : (m n : ℕ) → succ m ∔ n ≡ succ (m ∔ n)
succ-left m zero     = refl (succ m)
succ-left m (succ n) = ap succ (succ-left m n)

plus-comm : (m n : ℕ) → m ∔ n ≡ n ∔ m
plus-comm zero     n = zero-left n
plus-comm (succ m) n = succ-left m n ∙ ap succ (plus-comm m n)

_≤_ : ℕ → ℕ → Type
zero   ≤ n      = ℕ₁
succ m ≤ zero   = ℕ₀
succ m ≤ succ n = m ≤ n

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero     = *
≤-refl (succ n) = ≤-refl n

\end{code}

A subtraction x - y with the assumption le : y ≤ x is written

  x - y [ le ].

\begin{code}

_-_[_] : (m n : ℕ) → n ≤ m → ℕ
zero   - n      [ le ] = zero
succ m - zero   [ le ] = succ m
succ m - succ n [ le ] = m - n [ le ]

minus-property : (m n : ℕ) (le : n ≤ m) → (m - n [ le ]) ∔ n ≡ m
minus-property zero     zero     le = refl zero
minus-property (succ m) zero     le = refl (succ m)
minus-property (succ m) (succ n) le = ap succ (minus-property m n le)

max : ℕ → ℕ → ℕ
max zero     n        = n
max (succ m) zero     = succ m
max (succ m) (succ n) = succ (max m n)

left-≤-max : (m n : ℕ) → m ≤ max m n
left-≤-max zero     n        = *
left-≤-max (succ m) zero     = ≤-refl m
left-≤-max (succ m) (succ n) = left-≤-max m n

max-comm : (m n : ℕ) → max m n ≡ max n m
max-comm zero     zero     = refl zero
max-comm zero     (succ n) = refl (succ n)
max-comm (succ m) zero     = refl (succ m)
max-comm (succ m) (succ n) = ap succ (max-comm m n)

right-≤-max : (m n : ℕ) → n ≤ max m n
right-≤-max m n = transport (n ≤_) (max-comm n m) (left-≤-max n m)

\end{code}
