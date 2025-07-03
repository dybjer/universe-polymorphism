\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (_^_)

module marcs-example where

marc₀ : (X : 𝓤 ⊔ (𝓥 ⁺) ̇ ) → X ≡ (Σ A ꞉ 𝓥 ̇ , (A → X))
marc₀ X = {!!}

{-
In our system, we would simply write

marc₁ : (X :  𝓤 ̇ ) → X ≡ (Σ A ꞉ 𝓥 ̇ , (A → X)) with 𝓥 < 𝓤
marc₁ = {!!}

In an implementation of the system would infer 𝓥 < 𝓤

Agda works as follows: it infers

-- 𝓤 ⊔ 𝓥 ⁺ = 𝓤

Then the user infers:

-- 𝓥 < 𝓤

So the user can choose (as in marc₀):

-- 𝓤' := 𝓤 ⊔ 𝓥 ⁺

Then 𝓥 < 𝓤'

-}

\end{code}
