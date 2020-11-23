This is a variation of TarskiUniverseHierarchies.lagda using natural numbers as the levels.

\begin{code}

{-# OPTIONS --without-K #-}

-- {-# OPTIONS --no-positivity-check #-}


module TarskiUniverseHierarchieswithNaturals where

\end{code}

We first introduce notation for some standard MLTT basic types:

\begin{code}

data ℕ₀ : Set where

ℕ₀-induction : (P : ℕ₀ → Set) → (n : ℕ₀) → P n
ℕ₀-induction P ()

data  ℕ₁ : Set where
 * :  ℕ₁

ℕ₁-induction : (P :  ℕ₁ → Set) → P * → (n : ℕ₁) → P n
ℕ₁-induction P x * = x

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

ℕ-induction : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P(succ n)) → (n : ℕ) → P n
ℕ-induction P x f zero = x
ℕ-induction P x f (succ n) = f n (ℕ-induction P x f n)

\end{code}

And then for some standard MLTT type formers.

\begin{code}

data _+_ (A B : Set) : Set where
 inl : A → A + B
 inr : B → A + B

+-induction : (A B : Set) (P : A + B → Set)
            → ((a : A) → P (inl a)) → ((b : B) → P(inr b)) → (c : A + B) → P c
+-induction A B P f g (inl a) = f a
+-induction A B P f g (inr b) = g b

Π : (A : Set) → (A → Set) → Set
Π A B = (x : A) → B x

data Σ (A : Set) (B : A → Set) : Set where
 _,_ : (a : A) → B a → Σ A B

Σ-induction : (A : Set) (B : A → Set) (P : Σ A B → Set)
            → ((a : A) → (b : B a) → P(a , b))
            → (c : Σ A B) → P c
Σ-induction A B P f (x , y) = f x y

data W (A : Set) (B : A → Set) : Set where
 sup : (a : A) → (B a → W A B) → W A B

W-induction : (A : Set) (B : A → Set) (P : W A B → Set)
            → ((a : A) → (s : B a → W A B) → ((b : B a) → P(s b)) → P(sup a s))
            → (w : W A B) → P w
W-induction A B P f (sup a s) = f a s (λ (b : B a) → W-induction A B P f (s b))

data Id (A : Set) : A → A → Set where
 refl : (a : A) → Id A a a

Id-induction : (A : Set) (P : (x y : A) → Id A x y → Set)
             → ((x : A) → P x x (refl x))
             → (a b : A) → (r : Id A a b) → P a b r
Id-induction A P f a a (refl a) = f a

\end{code}


We define two universe hierarchies:

 * U  (cumulative by coercion) and

 * U' (cumulative on the nose)

both indexed by a set L of levels, which is given by the following
assumptions:

\begin{code}

L = ℕ
O = zero
_⁺ = succ

_⊔_ : L → L → L
zero ⊔ j = j
succ i ⊔ zero = succ i
succ i ⊔ succ j = succ (i ⊔ j)

\end{code}

We now define U and T by mutual induction-recursion:

\begin{code}

data U₀ : Set
T₀ : U₀ → Set

data U₀ where
 ⌜ℕ₀⌝   : U₀
 ⌜ℕ₁⌝   : U₀
 ⌜ℕ⌝    : U₀
 _⌜+⌝_  : U₀ → U₀ → U₀
 ⌜Π⌝    : (a : U₀) → (T₀ a → U₀) → U₀
 ⌜Σ⌝    : (a : U₀) → (T₀ a → U₀) → U₀
 ⌜W⌝    : (a : U₀) → (T₀ a → U₀) → U₀
 ⌜Id⌝   : (a : U₀) → T₀ a → T₀ a → U₀

T₀ ⌜ℕ₀⌝         = ℕ₀
T₀ ⌜ℕ₁⌝         = ℕ₁
T₀ ⌜ℕ⌝          = ℕ
T₀ (a ⌜+⌝ b)    = T₀ a + T₀ b
T₀ (⌜Π⌝ a b)    = Π (T₀ a) (λ x → T₀ (b x))
T₀ (⌜Σ⌝ a b)    = Σ (T₀ a) (λ x → T₀ (b x))
T₀ (⌜W⌝ a b)    = W (T₀ a) (λ x → T₀ (b x))
T₀ (⌜Id⌝ a x y) = Id (T₀ a) x y

data Next (U : Set) (T : U → Set) : Set where
 ⌜U⌝ : Next U T



U : L → Set
T : (i : L) → U i → Set




U zero = {!U'!}
 where

U (succ n) = {!!}

{-
data U' where
 ⌜ℕ₀⌝   : U' O
 ⌜ℕ₁⌝   : U' O
 ⌜ℕ⌝    : U' O
 ⌜+⌝    : (i j : L) → U₀ → U' j → U' (i ⊔ j)
 ⌜Π⌝    : (i j : L) (a : U₀) → (T' i a → U' j) → U' (i ⊔ j)
 ⌜Σ⌝    : (i j : L) (a : U₀) → (T' i a → U' j) → U' (i ⊔ j)
 ⌜W⌝    : (i j : L) (a : U₀) → (T' i a → U' j) → U' (i ⊔ j)
 ⌜Id⌝   : (i : L) (a : U₀) → T' i a → T' i a → U₀
 ⌜U⌝    : (i : L) → U' (i ⁺)
 ⌜Lift⌝ : (i j : L) → U₀ → U' (i ⊔ j)
-}

T i u = {!!}

{-
T O ⌜ℕ₀⌝                  = ℕ₀
T O ⌜ℕ₁⌝                  = ℕ₁
T O ⌜ℕ⌝                   = ℕ
T i (⌜+⌝ i j a b)  = T i a + T j b
T i (⌜Π⌝ i j a b)  = Π (T i a) (λ x → T j (b x))
T i (⌜Σ⌝ i j a b)  = Σ (T i a) (λ x → T j (b x))
T .(i ⊔ j) (⌜W⌝ i j a b)  = W (T i a) (λ x → T j (b x))
T i (⌜Id⌝ i a x y)        = Id (T i a) x y
T .(i ⁺) (⌜U⌝ i)          = U₀
T .(i ⊔ j) (⌜Lift⌝ i j a) = T i a
-}

\end{code}

Notice that the last equation is what gives cumulativity on the nose.
