------------------------------
-- The universe operator
------------------------------

module MLTT.SuperUniverse where

open import MLTT.MonomorphicSets hiding (U;T)
open import MLTT.Universe.Operator

mutual

-- the codes of the superuniverse

  data V : Set where
     n₀ : V
     n₁ : V
     _⊕_ : V → V → V
     σ : (a : V) → (S a → V) → V
     π : (a : V) → (S a → V) → V
     n : V
     w : (a : V) → (S a → V) → V
     i : (a : V) → S a → S a → V
--   V is closed under the "next universe" operator U, T, i e we have codes 
     u : (a : V) → (S a → V) → V
     t : (a : V) → (b : S a → V) → U (S a) (λ x → S (b x)) → V

-- the decoding map

  S : V → Set
  S n₀        = N₀
  S n₁        = N₁
  S (a ⊕ b)   = S a + S b
  S (σ a b)   = Σ (S a) (λ x → S (b x))
  S (π a b)   = Π (S a) (λ x → S (b x))
  S n         = N
  S (w a b)   = W (S a) (λ x → S (b x))
  S (i a b c) = I (S a) b c
  S (u a b)   = U (S a) (λ x → S (b x)) 
  S (t a b c) = T (S a) (λ x → S (b x)) c

-- we can build an infinite tower of universes inside the super universe

mutual
  u' : N → V
  u' O     = n₀
  u' (s m) = u (u' m) (t' m)

  t' : (m : N) → S (u' m) → V
  t' (s m) = t (u' m) (t' m)

-- and its limit

u-ω : V
u-ω = σ n u'

-- and an analogue of
-- largeType : Setω
-- largeType = (l : Level) → Set l

largeTypeV : V
largeTypeV = π n u'


