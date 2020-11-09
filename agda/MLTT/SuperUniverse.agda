------------------------------
-- The super universe
------------------------------

module MLTT.SuperUniverse where

open import MLTT.MonomorphicSets hiding (F)

-- If U, T is a family of sets (perceived as a universe)
-- then F U T, G U T is the next universe above it

mutual
  data F (U : Set) (T : U -> Set) : Set where
    n₀ : F U T
    n₁ : F U T
    _⊕_ : F U T -> F U T -> F U T
    σ : (a : F U T) -> (G U T a -> F U T) -> F U T
    π : (a : F U T) -> (G U T a -> F U T) -> F U T
    n : F U T
    w : (a : F U T) -> (G U T a -> F U T) -> F U T
    i : (a : F U T) -> G U T a -> G U T a -> F U T    
    u : F U T
    t : U → F U T -- the cumulativity map, the lift

  G : (U : Set) -> (T : U -> Set) -> F U T -> Set
  G U T n₀        = N₀
  G U T n₁        = N₁
  G U T (a ⊕ b)   = G U T a + G U T b
  G U T (σ a b)   = Σ (G U T a) (\x -> G U T (b x))
  G U T (π a b)   = Π (G U T a) (\x -> G U T (b x))
  G U T n         = N
  G U T (w a b)   = W (G U T a) (\x -> G U T (b x))
  G U T (i a b c) = I (G U T a) b c
  G U T u         = U
  G U T (t a)     = T a -- cumulativity on the nose
  
-- The super universe is closed
-- under the next universe operator
-- It contains the first universe,
-- since it is the next universe above the empty universe:
-- U₀ = F N₀ R₀ and T₀ = G N₀ R₀

mutual
  data V : Set where
     n₀ : V
     n₁ : V
     _⊕_ : V -> V -> V
     σ : (a : V) -> (S a -> V) -> V
     π : (a : V) -> (S a -> V) -> V
     n : V
     w : (a : V) -> (S a -> V) -> V
     i : (a : V) -> S a -> S a -> V
     f : (a : V) -> (S a -> V) -> V
     g : (a : V) -> (b : S a -> V) -> F (S a) (λ x -> S (b x)) -> V

  S : V -> Set
  S n₀        = N₀
  S n₁        = N₁
  S (a ⊕ b)   = S a + S b
  S (σ a b)   = Σ (S a) (\x -> S (b x))
  S (π a b)   = Π (S a) (\x -> S (b x))
  S n         = N
  S (w a b)   = W (S a) (\x -> S (b x))
  S (i a b c) = I (S a) b c
  S (f a b)   = F (S a) (\x -> S (b x))
  S (g a b c) = G (S a) (\x -> S (b x)) c


