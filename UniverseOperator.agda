------------------------------
-- The universe operator
------------------------------

module MLTT.UniverseOperator where

open import MLTT.MonomorphicSets hiding (U;T)
open import Agda.Primitive

-- If A, B is a family of sets (perceived as a universe)
-- then U A B, T A B is the next universe above it

mutual
  data U (A : Set) (B : A -> Set) : Set where
    n₀ : U A B
    n₁ : U A B
    _⊕_ : U A B → U A B → U A B
    σ : (a : U A B) → (T A B a → U A B) → U A B
    π : (a : U A B) → (T A B a → U A B) → U A B
    n : U A B
    w : (a : U A B) → (T A B a → U A B) → U A B
    i : (a : U A B) → T A B a → T A B a → U A B    
    u : U A B     
    t : A → U A B
    
-- If A is the previous universe and B is the decoding map,
-- then u is the code for the previous universe
-- and t returns codes for the results of the decoding map:

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
  T A B (t a)     = B a

-- The zeroth universe U₀, T₀ is the empty universe

U₀ = N₀
T₀ : U₀ → Set
T₀ ()

-- The first universe U₁, T₁ is the universe above the empty universe

U₁ = U N₀ T₀
T₁ = T N₀ T₀

-- The second universe U₂, T₂ is the universe above the first universe

U₂ = U U₁ T₁
T₂ = T U₁ T₁

-- etc

-- We can internalize the infinite tower of universes:

mutual
  U' : N → Set
  U' O = U₀
  U' (s l) = U (U' l) (T' l)

  T' : (l : N) → U' l → Set 
  T' (s l) = T (U' l) (T' l)

-- note that N is a "universe" closed only under the empty universe
-- and next universe operator:
-- 0 is a code for the empty universe
-- and s encodes the next universe operator

-- we can now define universe polymorphic notions:

n' : (l : N) → U' (s l)
n' l = n {U' l} {T' l}

⊕' : (l : N) → U' l → U' l → U' l
⊕' (s l) a b = a ⊕ b

σ' : (l : N) → (a : U' l) → (T' l a → U' l) → U' l
σ' (s l) a b = σ a b

i' : (l : N) → (a : U' l) → T' l a → T' l a → U' l
i' (s l) a x y = i a x y

-- we can also define the limit of U' l:

U-ω : Set
U-ω = Σ N U'

T-ω : U-ω → Set
T-ω (l , a) = T' l a

-- Note that the tower U' 1, U' 2, U' 3 : Set is different from
-- Agda's built-in tower Set₀, Set₁, Set₂, ...

set₀ : Set₁
set₀ = Set₀

set₁ : Set₂
set₁ = Set₁

set₂ : Set₃
set₂ = Set₂

-- etc

-- Agda also has a type Level of levels. It is different from N,
-- but we can inject numbers into levels:

nToLevel : N → Level
nToLevel O     = lzero
nToLevel (s l) = lsuc (nToLevel l)

-- Moreover, Agda has a special type Setω, a "kind" which can only be used in restricted ways

largeType : Setω
largeType = (l : Level) → Set l

-- We can make an analogue of this type using the tower U' l

largeType' : Set
largeType' = (l : N) → U' l


