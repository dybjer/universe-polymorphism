------------------------------------------------------------------------
-- Martin-Löf type theory 
------------------------------------------------------------------------

-- We present the intensional monomorphic version of Martin-Löf type theory from 1986,
-- see Nordström, Petersson, and Smith 1989. (It is not exactly the same theory
-- since Agda has (x : A) -> B : Set provided A : Set, B : (x : A) -> Set, 
-- whereas (x : A) -> B in Martin-Löf type theory is only a type.)

module MLTT.MonomorphicSets where

data N₀ : Set where

R₀ : (C : N₀ -> Set) -> (c : N₀) -> C c
R₀ C ()

data  N₁ : Set where
  0₁ : N₁

R₁ : (C :  N₁ -> Set) -> C 0₁ -> (c :  N₁) -> C c
R₁ C d 0₁ = d

data _+_ (A B : Set) : Set where
  i : A -> A + B
  j : B -> A + B

D : (A B : Set) -> (C : A + B -> Set) 
  -> ((a : A) -> C (i a)) -> ((b : B) -> C (j b)) -> (c : A + B) -> C c
D A B C d e (i a) = d a
D A B C d e (j b) = e b

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> B a -> Σ A B

E : (A : Set) -> (B : A -> Set) -> (C : Σ A B -> Set)
  -> ((x : A) -> (y : B x) -> C (x , y))
  -> (z : Σ A B) -> C z
E A B C d (x , y) = d x y

-- in intensional type theory E (split) is not derivable from the projections,
-- hence it is taken as a primitive

data Π (A : Set) (B : A -> Set) : Set where
  Λ : ((a : A) -> B a) -> Π A B

F :  (A : Set) -> (B : A -> Set) -> (C : Π A B -> Set)
  -> ((b : (x : A) -> B x) -> C (Λ b))
  -> (z : Π A B) -> C z
F A B C d (Λ b) = d b

-- in intensional type theory F (funsplit) is more general than application and
-- taken as a primitive

-- In the Agda version of Martin-Löf type theory, the framework function
-- space (x : A) -> B x more or less replaces Π A B.

data I (A : Set) : A -> A -> Set where
  r : (a : A) -> I A a a

J : (A : Set) -> (C : (x y : A) -> I A x y -> Set)
  -> ((x : A) -> C x x (r x))
  -> (a b : A) -> (c : I A a b) -> C a b c
J A C d .b b (r .b) = d b

K : (A : Set) -> (C : (x : A) -> I A x x -> Set)
  -> ((x : A) -> C x (r x))
  -> (a : A) -> (c : I A a a) -> C a c
K A C d b (r .b) = d b

data N : Set where
  O : N
  s : N -> N

R : (C : N -> Set) -> C O -> ((n : N) -> C n -> C (s n)) -> (c : N) -> C c
R C d e O     = d
R C d e (s n) = e n (R C d e n)

data W (A : Set) (B : A -> Set) : Set where
  sup : (a : A) -> (b : B a -> W A B) -> W A B

wrec : (A : Set) -> (B : A -> Set) -> (C : W A B -> Set) 
     -> ((a : A) -> (b : B a -> W A B) -> ((x : B a) -> C (b x)) -> C (sup a b)) 
     -> (c : W A B) -> C c
wrec A B C d (sup a b) = d a b (\x -> wrec A B C d (b x))

mutual
  data U : Set where
     n₀ : U
     n₁ : U
     _⊕_ : U -> U -> U
     σ : (a : U) -> (T a -> U) -> U
     π : (a : U) -> (T a -> U) -> U
     n : U
     w : (a : U) -> (T a -> U) -> U
     i : (a : U) -> T a -> T a -> U

  T : U -> Set
  T n₀        = N₀
  T n₁        = N₁
  T (a ⊕ b)   = T a + T b
  T (σ a b)   = Σ (T a) (\x -> T (b x))
  T (π a b)   = Π (T a) (\x -> T (b x))
  T n         = N
  T (w a b)   = W (T a) (\x -> T (b x))
  T (i a b c) = I (T a) b c




