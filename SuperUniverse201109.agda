------------------------------
-- The super universe
------------------------------

module MLTT.SuperUniverse201109 where

open import MLTT.MonomorphicSets hiding (U;T) 

-- If A, B is a family of sets (perceived as a universe)
-- then U A B, T A B is the next universe above it

mutual
  data U (A : Set) (B : A -> Set) : Set where
    n₀ : U A B
    n₁ : U A B
    _⊕_ : U A B → U A B → U A B
-- cf  σ : (a : U₀) → (B a → U₀) → U₀ for the first universe
    σ : (a : U A B) → (T A B a → U A B) → U A B
    π : (a : U A B) → (T A B a → U A B) → U A B
    n : U A B
    w : (a : U A B) → (T A B a → U A B) → U A B
    i : (a : U A B) → T A B a → T A B a → U A B    
    u : U A B     -- the code for the previous universe
    t : A → U A B -- codes for the results of the cumulativity map,
                  -- "lift" in Agda terminology

  T : (A : Set) → (B : A → Set) → U A B → Set
  T A B n₀        = N₀
  T A B n₁        = N₁
  T A B (a ⊕ b)   = T A B a + T A B b
  T A B (σ a b)   = Σ (T A B a) (λ x → T A B (b x))
  T A B (π a b)   = Π (T A B a) (λ x → T A B (b x))
  T A B n         = N
  T A B (w a b)   = W (T A B a) (λ x → T A B (b x))
  T A B (i a b c) = I (T A B a) b c
  T A B u         = A
  T A B (t a)     = B a -- cumulativity on the nose

-- The zeroth universe U₀, T₀ is the empty universe

U₀ = N₀
T₀ : U₀ → Set
T₀ ()

-- The first universe U₁, T₁ is the universe above the empty universe

U₁ = U N₀ T₀
T₁ = T N₀ T₀

-- etc

-- We can internalize the infinite tower of universes:

mutual
  U' : N → Set
  U' O = N₀
  U' (s m) = U (U' m) (T' m)

  T' : (m : N) → U' m → Set 
  T' (s m) = T (U' m) (T' m)

-- and define universe polymorphic notions:

n' : (m : N) → U' (s m)
n' m = n {U' m} {T' m}

⊕' : (m : N) → U' m → U' m → U' m
⊕' (s m) a b = a ⊕ b

σ' : (m : N) → (a : U' m) → (T' m a → U' m) → U' m
σ' (s m) a b = σ a b

i' : (m : N) → (a : U' m) → T' m a → T' m a → U' m
i' (s m) a x y = i a x y

-- we can also define the limit of U' n:

U-ω : Set
U-ω = Σ N U'

T-ω : U-ω → Set
T-ω (m , a) = T' m a

mutual
  data V : Set where
     n₀ : V
     n₁ : V
     _⊕_ : V → V → V
     σ : (a : V) → (S a → V) → V
     π : (a : V) → (S a → V) → V
     n : V
     w : (a : V) → (S a → V) → V
     i : (a : V) → S a → S a → V
--   V is closed under the "next universe operator U,T", i e under 
     u : (a : V) → (S a → V) → V
     t : (a : V) → (b : S a → V) → U (S a) (λ x → S (b x)) → V

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

mutual
  u' : N → V
  u' O = n₀
  u' (s m) = u (u' m) (t' m)

  t' : (m : N) → S (u' m) → V
  t' (s m) = t (u' m) (t' m)

u-ω : V
u-ω = σ n u'

