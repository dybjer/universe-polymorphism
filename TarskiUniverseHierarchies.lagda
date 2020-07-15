Peter Dybjer defines, in the Agda wiki, "the first universe à la
Tarski" by induction-recursion:

http://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.RulesForTheStandardSetFormers

Here we define two hierarchies of universes à la Tarski, indexed by a
successor-sup-semilattice, one cumulative by coercion, and the other
cumulative on the nose.

The Agda type Set (or Set₀) will host all these universes à la Tarski:

\begin{code}

{-# OPTIONS --without-K #-}

{-# OPTIONS --no-positivity-check #-} -- See (*) below.

module TarskiUniverseHierarchies where

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
W-induction A B P f (sup a s) = f a s (λ(b : B a) → W-induction A B P f (s b))

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

module _ (L   : Set)
         (O   : L)
         (_⁺  : L → L)
         (_⊔_ : L → L → L)
       where

\end{code}

We don't need to assume the successor-sup-semilattice equations for
the data (O , _⊔_, _⁺) in the definitions of U and U'. Moreover,we
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

 ×' :  (i j : L) → U i → U j → U (i ⊔ j)
 ×' i j a b = ⌜Σ⌝ i j a (λ _ → b)

 Lift : (i j : L) → U i → U (i ⊔ j)
 Lift i j a = ×' i j a (⌜ℕ₁⌝ j)

 lift : (i j : L) (a : U i) → T i a → T (i ⊔ (i ⊔ j)) (Lift i (i ⊔ j) a)
 lift  i j a x = x , *

 Lift-induction : (i j k : L) (a : U i) (b : T (i ⊔ j) (Lift i j a) → U k)
                → ((x : T i a) → T k (b (lift i j a x)))
                → (l : T (i ⊔ j) (Lift i j a)) → T k (b l)
 Lift-induction i j k a b φ (x , *) = φ x

\end{code}

In the second universe hierarchy U', we have lifting as primitive, and
we place the basic types in the first universe only. This time we need
the bottom element O : L, but we still don't need the
succ-sup-semilatice equations, as already remarked above.

We now define U' and T' by mutual induction-recursion:

\begin{code}

 data U' : L → Set
 T' : (i : L) → U' i → Set

 data U' where
  ⌜ℕ₀⌝   : U' O
  ⌜ℕ₁⌝   : U' O
  ⌜ℕ⌝    : U' O
  ⌜+⌝    : (i j : L) → U' i → U' j → U' (i ⊔ j)
  ⌜Π⌝    : (i j : L) (a : U' i) → (T' i a → U' j) → U' (i ⊔ j)
  ⌜Σ⌝    : (i j : L) (a : U' i) → (T' i a → U' j) → U' (i ⊔ j)
  ⌜W⌝    : (i j : L) (a : U' i) → (T' i a → U' j) → U' (i ⊔ j)
  ⌜Id⌝   : (i : L) (a : U' i) → T' i a → T' i a → U' i
  ⌜U⌝    : (i : L) → U' (i ⁺)
  ⌜Lift⌝ : (i j : L) → U' i → U' (i ⊔ j)

 T' O ⌜ℕ₀⌝                  = ℕ₀
 T' O ⌜ℕ₁⌝                  = ℕ₁
 T' O ⌜ℕ⌝                   = ℕ
 T' .(i ⊔ j) (⌜+⌝ i j a b)  = T' i a + T' j b
 T' .(i ⊔ j) (⌜Π⌝ i j a b)  = Π (T' i a) (λ x → T' j (b x))
 T' .(i ⊔ j) (⌜Σ⌝ i j a b)  = Σ (T' i a) (λ x → T' j (b x))
 T' .(i ⊔ j) (⌜W⌝ i j a b)  = W (T' i a) (λ x → T' j (b x))
 T' i (⌜Id⌝ i a x y)        = Id (T' i a) x y
 T' .(i ⁺) (⌜U⌝ i)          = U' i
 T' .(i ⊔ j) (⌜Lift⌝ i j a) = T' i a

\end{code}

Notice that the last equation is what gives cumulativity on the nose.

TODO. Write CwF definitions.
