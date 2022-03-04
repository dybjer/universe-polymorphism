\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (_^_)

module marcs-example where

open import UF-Equiv
open import UF-Classifiers
open import UF-Univalence
open import UF-FunExt

marc : (X : {!!} ̇ ) → X ≡ (Σ A ꞉ {!!} ̇ , (A → X))
marc X = {!!}

notice-that : is-univalent 𝓤
            → funext 𝓤 (𝓤 ⁺)
            → (X : 𝓤 ̇ ) → (Σ A ꞉ 𝓤 ̇ , (A → X)) ≃ (X → 𝓤 ̇)
notice-that ua fe X = map-classification ua fe X

marc' : (X : {!!} ̇ ) → X ≃ (X → 𝓤 ̇)
marc' X = {!!}

model-of-CZF : 𝓤 ⁺ ⊔ 𝓥 ̇ → ((𝓤 ⁺) ⊔ 𝓥)⁺ ̇
model-of-CZF {𝓤} X = X ≡ (X → 𝓤 ̇)
model-of-CZF' : 𝓤 ⁺ ⊔ 𝓥 ̇ → (𝓤 ⁺) ⊔ 𝓥 ̇
model-of-CZF' {𝓤} X = X ≃ (X → 𝓤 ̇)


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
