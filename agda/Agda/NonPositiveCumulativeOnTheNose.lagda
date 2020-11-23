This uses --no-positivity-check and is inconsistent if e.g. i⁺ = i.

\begin{code}

{-# OPTIONS --without-K #-}
{-# OPTIONS --no-positivity-check #-}

open import MLTT

module NonPositiveCumulativeOnTheNose
        (L   : Set)
        (O   : L)
        (_⁺  : L → L)
        (_⊔_ : L → L → L)
       where

data U : L → Set
T : (i : L) → U i → Set

data U where
 ⌜ℕ₀⌝   : U O
 ⌜ℕ₁⌝   : U O
 ⌜ℕ⌝    : U O
 ⌜+⌝    : (i j : L) → U i → U j → U (i ⊔ j)
 ⌜Π⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜Σ⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜W⌝    : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜Id⌝   : (i : L) (a : U i) → T i a → T i a → U i
 ⌜U⌝    : (i : L) → U (i ⁺)
 ⌜Lift⌝ : (i j : L) → U i → U (i ⊔ j)

T O ⌜ℕ₀⌝                  = ℕ₀
T O ⌜ℕ₁⌝                  = ℕ₁
T O ⌜ℕ⌝                   = ℕ
T .(i ⊔ j) (⌜+⌝ i j a b)  = T i a + T j b
T .(i ⊔ j) (⌜Π⌝ i j a b)  = Π (T i a) (λ x → T j (b x))
T .(i ⊔ j) (⌜Σ⌝ i j a b)  = Σ (T i a) (λ x → T j (b x))
T .(i ⊔ j) (⌜W⌝ i j a b)  = W (T i a) (λ x → T j (b x))
T i (⌜Id⌝ i a x y)        = Id (T i a) x y
T .(i ⁺) (⌜U⌝ i)          = U i
T .(i ⊔ j) (⌜Lift⌝ i j a) = T i a

\end{code}
