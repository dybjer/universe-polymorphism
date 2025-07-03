------------------------------
-- The universe operator
------------------------------

module MLTT.UniverseFullReflection where

open import MLTT.MonomorphicSets hiding (U;T)

-- We define the first universe closed only under Π for the purpose of illustration

mutual
  data U₁ : Set where
     π₁ : (a : U₁) → (T₁ a → U₁) → U₁

  T₁ : U₁ → Set
  T₁ (π₁ a b) = Π (T₁ a) (λ x → T₁ (b x))

-- The second universe also has a code for the first universe:

mutual
  data U₂ : Set where
     π₂ : (a : U₂) → (T₂ a → U₂) → U₂
     u₁₂ : U₂

  T₂ : U₂ → Set
  T₂ (π₂ a b) = Π (T₂ a) (λ x → T₂ (b x))
  T₂ u₁₂ = U₁

-- We try to define the cumulativity (lifting) map by universe elimination:

t₁₂ : U₁ → U₂
t₁₂ (π₁ a b) = π₂ (t₁₂ a) (λ x → t₁₂ (b {! x!}))

-- We have x : T₂ (t₁₂ a), but b expects an argument of type T₁ a,
-- and these types are not definitionally equal (convertible)
