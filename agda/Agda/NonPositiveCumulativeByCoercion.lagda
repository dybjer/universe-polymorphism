A "cumulative by coercion" hierarchy of universes à la Tarski, indexed
by a successor-sup-semilattice. This requires --no-positivity-check and is inconsistent if we have e.g. i⁺ = i, as in this case we get type in type.

The Agda type Set (or Set₀) will host all these universes à la Tarski.

\begin{code}

{-# OPTIONS --without-K #-}
{-# OPTIONS --no-positivity-check #-}

open import MLTT

module NonPositiveCumulativeByCoercion
        (L   : Set)
        (O   : L)
        (_⁺  : L → L)
        (_⊔_ : L → L → L)
       where

\end{code}

We don't need to assume the successor-sup-semilattice equations for
the data (O , _⊔_, _⁺) in the definitions of U and U'. Moreover, we
don't need to assume O : L for the definition of U.

We now define U and T by mutual induction-recursion:

\begin{code}

data U : L → Set
T : (i : L) → U i → Set

data U where
 ⌜ℕ₀⌝  : (i : L) → U i
 ⌜ℕ₁⌝  : (i : L) → U i
 ⌜ℕ⌝   : (i : L) → U i
 ⌜+⌝   : (i j : L) → U i → U j → U (i ⊔ j)
 ⌜Π⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜Σ⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜W⌝   : (i j : L) (a : U i) → (T i a → U j) → U (i ⊔ j)
 ⌜Id⌝  : (i : L) (a : U i) → T i a → T i a → U i
 ⌜U⌝   : (i : L) → U (i ⁺)

T i (⌜ℕ₀⌝ i)             = ℕ₀
T i (⌜ℕ₁⌝ i)             = ℕ₁
T i (⌜ℕ⌝ i)              = ℕ
T .(i ⊔ j) (⌜+⌝ i j a b) = T i a + T j b
T .(i ⊔ j) (⌜Π⌝ i j a b) = Π (T i a) (λ x → T j (b x))
T .(i ⊔ j) (⌜Σ⌝ i j a b) = Σ (T i a) (λ x → T j (b x))
T .(i ⊔ j) (⌜W⌝ i j a b) = W (T i a) (λ x → T j (b x))
T i (⌜Id⌝ i a x y)       = Id (T i a) x y
T .(i ⁺) (⌜U⌝ i)         = U i

\end{code}

Then lifting is definable:

\begin{code}

⌜×⌝ :  (i j : L) → U i → U j → U (i ⊔ j)
⌜×⌝ i j a b = ⌜Σ⌝ i j a (λ _ → b)

Lift : (i j : L) → U i → U (i ⊔ j)
Lift i j a = ⌜×⌝ i j a (⌜ℕ₁⌝ j)

lift : (i j : L) (a : U i) → T i a → T (i ⊔ (i ⊔ j)) (Lift i (i ⊔ j) a)
lift  i j a x = x , *

Lift-induction : (i j k : L) (a : U i) (b : T (i ⊔ j) (Lift i j a) → U k)
               → ((x : T i a) → T k (b (lift i j a x)))
               → (l : T (i ⊔ j) (Lift i j a)) → T k (b l)
Lift-induction i j k a b φ (x , *) = φ x

\end{code}
