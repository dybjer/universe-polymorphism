Peter Dybjer defines, in the Agda wiki, "the first universe à la
Tarski" by induction-recursion:

http://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.RulesForTheStandardSetFormers

Here we define two hierarchies of universes à la Tarski, indexed by a
successor-sup-semilattice, one cumulative by coercion, and the other
cumulative on the nose.

The Agda type Set (or Set₀) will host all these universes à la Tarski.

\begin{code}

{-# OPTIONS --without-K #-}

{-# OPTIONS --no-positivity-check #-}

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

syntax Π X (λ x → y) = Π x ꞉ X , y

record Σ (A : Set) (B : A → Set) : Set where
 constructor
   _,_
 field
   pr₁ : A
   pr₂ : B pr₁

open Σ

syntax Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : (A : Set) (B : A → Set) (P : Σ A B → Set)
            → ((a : A) → (b : B a) → P(a , b))
            → (c : Σ A B) → P c
Σ-induction A B P f (x , y) = f x y

data W (A : Set) (B : A → Set) : Set where
 sup : (a : A) → (B a → W A B) → W A B

syntax W X (λ x → y) = W x ꞉ X , y

W-induction : (A : Set) (B : A → Set) (P : W A B → Set)
            → ((a : A) → (s : B a → W A B) → ((b : B a) → P(s b)) → P(sup a s))
            → (w : W A B) → P w
W-induction A B P f (sup a s) = f a s (λ (b : B a) → W-induction A B P f (s b))

data Id (A : Set) : A → A → Set where
 refl : (a : A) → Id A a a

infix 0 _≡_
_≡_ : {A : Set} → A → A → Set
x ≡ y = Id _ x y

Id-induction : (A : Set) (P : (x y : A) → Id A x y → Set)
             → ((x : A) → P x x (refl x))
             → (a b : A) → (r : Id A a b) → P a b r
Id-induction A P f a a (refl a) = f a

ap : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl _) = refl _

transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport B (refl _) b = b

\end{code}


We define two universe hierarchies,

 * U  (cumulative by coercion) and

 * U' (cumulative on the nose)

both indexed by a set L of levels, which is given by the following
assumptions:

\begin{code}

module cumulative-by-coercion
        (L   : Set)
        (O   : L)
        (_⁺  : L → L)
        (_⊔_ : L → L → L)
       where

\end{code}

We don't need to assume the successor-sup-semilattice equations for
the data (O , _⊔_, _⁺) in the definitions of U and U'. Moreover, we
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

The following is adapted from Peters files (and it is due to Palmgren
and ?). It just changes notation.

A universe is just a pair (U , T) with

  * U : Set (the carrier), and
  * T : U → Set (the structure).

The following constructs an abstract universe (U' , T') from an
abstract universe (U , T), its successor.

\begin{code}

module successor (U : Set) (T : U -> Set) where

  data U' : Set
  T' : U' → Set

  data U' where
    ⌜ℕ₀⌝  : U'
    ⌜ℕ₁⌝  : U'
    ⌜ℕ⌝   : U'
    _⌜+⌝_ : U' → U' → U'
    ⌜Σ⌝   : (a : U') → (T' a → U') → U'
    ⌜Π⌝   : (a : U') → (T' a → U') → U'
    ⌜W⌝   : (a : U') → (T' a → U') → U'
    ⌜Id⌝  : (a : U') → T' a → T' a → U'
    ⌜U⌝   : U'
    ⌜T⌝   : U → U'

  T' ⌜ℕ₀⌝         = ℕ₀
  T' ⌜ℕ₁⌝         = ℕ₁
  T' ⌜ℕ⌝          = ℕ
  T' (a ⌜+⌝ b)    = T' a + T' b
  T' (⌜Σ⌝ a b)    = Σ (T' a) (λ x → T' (b x))
  T' (⌜Π⌝ a b)    = Π (T' a) (λ x → T' (b x))
  T' (⌜W⌝ a b)    = W (T' a) (λ x → T' (b x))
  T' (⌜Id⌝ a b c) = Id (T' a) b c
  T' ⌜U⌝          = U
  T' (⌜T⌝ a)      = T a

  carrier    = U'
  structure  = T'

\end{code}

The super-universe (V , S).

\begin{code}

module based-on-peters-Agda-rendering-of-palmgren where

 data V : Set
 S : V → Set

\end{code}

We also define (U , T) as follows, for the sake of readability of the
definition of (V , S).

We think of a pair (u , t), with u : V and t : S u → V, as an
"internal universe".

Then S u is a Set and λ (a : S u) → S (t a) is a family S u → Set, and
hence the pair (S u , λ (a : S u) → S (t a)) is the external version
of the internal universe (u , t). We define (U u t , T u t) to be the
successor universe of this external version.

\begin{code}

 U : (u : V) (t : S u → V) → Set
 T : (u : V) (t : S u → V) → U u t → Set

 U u t = successor.carrier   (S u) (λ (a : S u) → S (t a))
 T u t = successor.structure (S u) (λ (a : S u) → S (t a))

 data V where
   ⌜ℕ₀⌝  : V
   ⌜ℕ₁⌝  : V
   ⌜ℕ⌝   : V
   _⌜+⌝_ : V → V → V
   ⌜Σ⌝   : (a : V) → (S a → V) → V
   ⌜Π⌝   : (a : V) → (S a → V) → V
   ⌜W⌝   : (a : V) → (S a → V) → V
   ⌜Id⌝  : (a : V) → S a → S a → V
   ⌜U⌝   : (u : V) → (S u → V) → V
   ⌜T⌝   : (u : V) (t : S u → V) → U u t → V

 S ⌜ℕ₀⌝         = ℕ₀
 S ⌜ℕ₁⌝         = ℕ₁
 S ⌜ℕ⌝          = ℕ
 S (a ⌜+⌝ b)    = S a + S b
 S (⌜Σ⌝ a b)    = Σ (S a) (λ (x : S a) → S (b x))
 S (⌜Π⌝ a b)    = Π (S a) (λ (x : S a) → S (b x))
 S (⌜W⌝ a b)    = W (S a) (λ (x : S a) → S (b x))
 S (⌜Id⌝ a x y) = Id (S a) x y
 S (⌜U⌝ u t)    = U u t
 S (⌜T⌝ u t a)  = T u t a

\end{code}

An ℕ-indexed tower of universes v n, where we choose the first
universe to be empty, but then we work only with v (succ n):

\begin{code}

 internal-universe : Set
 internal-universe = Σ u ꞉ V , (S u → V)

 Carrier : internal-universe → Set
 Carrier (u , t) = S u

 Structure : (i : internal-universe) → Carrier i → Set
 Structure (u , t) a = S (t a)

 next : internal-universe → internal-universe
 next (u , t) = ⌜U⌝ u t , ⌜T⌝ u t

 v : ℕ → internal-universe
 v zero     = ⌜ℕ₀⌝ , ℕ₀-induction (λ _ → V)
 v (succ x) = next (v x)

 𝓥 : ℕ → Set
 𝓥 n = Carrier (v (succ n))

 𝓢 : (n : ℕ) → 𝓥 n → Set
 𝓢 n = Structure (v (succ n))

 data _≡₁_ {A : Set₁} : A → A → Set₁ where
   refl : (a : A) → a ≡₁ a

 Lift-succ : (n : ℕ) → 𝓥 n → 𝓥 (succ n)
 Lift-succ _ = successor.⌜T⌝

 𝓢-succ : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (Lift-succ n a) ≡₁ 𝓢 n a
 𝓢-succ n a = refl _

 𝓢-succ→ : (n : ℕ) (a : 𝓥 n) → 𝓢 n a → 𝓢 (succ n) (Lift-succ n a)
 𝓢-succ→ n a x = x

 𝓢-succ← : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (Lift-succ n a) → 𝓢 n a
 𝓢-succ← n a x = x
 infixl 10 _∔_
 _∔_ : ℕ → ℕ → ℕ
 x ∔ zero   = x
 x ∔ succ y = succ (x ∔ y)

 Lift₀ : (n : ℕ) → 𝓥 zero → 𝓥 n
 Lift₀ zero     a = a
 Lift₀ (succ n) a = Lift-succ n (Lift₀ n a)

 Lift-+  : (n k : ℕ) → 𝓥 n → 𝓥 (n ∔ k)
 Lift-+ n zero     a = a
 Lift-+ n (succ k) a = Lift-succ (n ∔ k) (Lift-+ n k a)

 _≤_ : ℕ → ℕ → Set
 zero   ≤ n      = ℕ₁
 succ m ≤ zero   = ℕ₀
 succ m ≤ succ n = m ≤ n

 ≤-refl : (n : ℕ) → n ≤ n
 ≤-refl zero     = *
 ≤-refl (succ n) = ≤-refl n

 _-_[_] : (m n : ℕ) → n ≤ m → ℕ
 zero     - n        [ le ] = zero
 (succ m) - zero     [ *  ] = succ m
 (succ m) - (succ n) [ le ] = m - n [ le ]

 minus-property : (m n : ℕ) (le : n ≤ m) → (m - n [ le ]) ∔ n ≡ m
 minus-property zero     zero     *  = refl zero
 minus-property (succ m) zero     *  = refl (succ m)
 minus-property (succ m) (succ n) le = ap succ (minus-property m n le)

 max : ℕ → ℕ → ℕ
 max zero     n        = n
 max (succ m) zero     = succ m
 max (succ m) (succ n) = succ (max m n)

 ≤-max : (m n : ℕ) → m ≤ max m n
 ≤-max zero     n        = *
 ≤-max (succ m) zero     = ≤-refl m
 ≤-max (succ m) (succ n) = ≤-max m n

 max-minus-property : (m n : ℕ) → (max m n - m [ ≤-max m n ]) ∔ m ≡ max m n
 max-minus-property m n = minus-property (max m n) m (≤-max m n)

 max-comm : (m n : ℕ) → max m n ≡ max n m
 max-comm zero     zero     = refl zero
 max-comm zero     (succ n) = refl (succ n)
 max-comm (succ m) zero     = refl (succ m)
 max-comm (succ m) (succ n) = ap succ (max-comm m n)

 LiftR   : (m n : ℕ) → 𝓥 n → 𝓥 (max m n)
 LiftR m n a = {!!}

 Lift-L-max : (m n : ℕ) → 𝓥 m → 𝓥 (max m n)
 Lift-L-max m n a = t (max m n - m [ ≤-max m n ] ∔ m) (max m n) (max-minus-property m n) b
  where
   t : (x y : ℕ) → Id ℕ x y → 𝓥 x → 𝓥 y
   t x x (refl x) a = a
   b : 𝓥 (max m n - m [ ≤-max m n ] ∔ m)
   b = Lift-+ m {!max m n - m [ ≤-max m n ]!} a
   -- Lift-+ m (max m n - m [ ≤-max m n ]) ?


 Lift-L-max→ : (m n : ℕ) (a : 𝓥 m) → 𝓢 m a → 𝓢 (max m n) (Lift-L-max m n a)
 Lift-L-max→ m n a x = {!!}

 Lift-L-max← : (m n : ℕ) (a : 𝓥 m) → 𝓢 (max m n) (Lift-L-max m n a) → 𝓢 m a
 Lift-L-max← m n a x = {!!}


 Lift-R-max   : (m n : ℕ) → 𝓥 n → 𝓥 (max m n)
 Lift-R-max zero     n a        = a
 Lift-R-max (succ m) zero a     = Lift₀ (succ m) a
 Lift-R-max (succ m) (succ n) a = {!!}


 module version₀ where

   module _ (n : ℕ) where

     |ℕ₀|   : 𝓥 n
     |ℕ₁|   : 𝓥 n
     |ℕ|    : 𝓥 n
     _|+|_  : 𝓥 n → 𝓥 n → 𝓥 n
     |Σ|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
     |Π|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
     |W|    : (a : 𝓥 n) → (𝓢 n a → 𝓥 n) → 𝓥 n
     |Id|   : (a : 𝓥 n) → 𝓢 n a → 𝓢 n a → 𝓥 n
     |U|    : 𝓥 n
     |T|    : 𝓥 n → 𝓥 (succ n)

     |ℕ₀|   = successor.⌜ℕ₀⌝
     |ℕ₁|   = successor.⌜ℕ₁⌝
     |ℕ|    = successor.⌜ℕ⌝
     _|+|_  = successor._⌜+⌝_
     |Σ|    = successor.⌜Σ⌝
     |Π|    = successor.⌜Π⌝
     |W|    = successor.⌜W⌝
     |Id|   = successor.⌜Id⌝
     |U|    = successor.⌜U⌝
     |T|    = successor.⌜T⌝

\end{code}

The equations that should hold definitionally indeed do:

\begin{code}

     |ℕ₀|-eq : 𝓢 n |ℕ₀| ≡₁ ℕ₀
     |ℕ₁|-eq : 𝓢 n |ℕ₁| ≡₁ ℕ₁
     |ℕ|-eq  : 𝓢 n |ℕ|  ≡₁ ℕ
     |+|-eq  : (a b : 𝓥 n) → 𝓢 n (a |+| b) ≡₁ (𝓢 n a + 𝓢 n b)
     |Σ|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Σ| a b) ≡₁ (Σ x ꞉ 𝓢 n a , 𝓢 n (b x))
     |Π|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Π| a b) ≡₁ (Π x ꞉ 𝓢 n a , 𝓢 n (b x))
     |W|-eq  : (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|W| a b) ≡₁ (W x ꞉ 𝓢 n a , 𝓢 n (b x))

     |ℕ₀|-eq    = refl _
     |ℕ₁|-eq    = refl _
     |ℕ|-eq     = refl _
     |+|-eq a b = refl _
     |Σ|-eq a b = refl _
     |Π|-eq a b = refl _
     |W|-eq a b = refl _

\end{code}

These equations need to go outside the above anonymous module, as they
using varying n's:

\begin{code}

   |U|-eq : (n : ℕ) → 𝓢 (succ n) (|U| (succ n)) ≡₁ 𝓥 n
   |T|-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (|T| n a) ≡₁ 𝓢 n a

   |U|-eq n   = refl _
   |T|-eq n a = refl _

\end{code}

We now try with joins of levels (max on natural numbers). Because max
is not commutative on the nose, we need two lift functions for the
code below to type check without transports.

\begin{code}

 module version₁ where

     |ℕ₀|   : (n : ℕ) → 𝓥 n
     |ℕ₁|   : (n : ℕ) → 𝓥 n
     |ℕ|    : (n : ℕ) → 𝓥 n
     _|+|_  : (m n : ℕ) → 𝓥 m → 𝓥 n → 𝓥 (max m n)
     |Σ|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
     |Π|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
     |W|    : (m n : ℕ) → (a : 𝓥 m) → (𝓢 m a → 𝓥 n) → 𝓥 (max m n)
     |Id|   : (n : ℕ) → (a : 𝓥 n) → 𝓢 n a → 𝓢 n a → 𝓥 n
     |U|    : (n : ℕ) → 𝓥 n
     |T|    : (n : ℕ) → 𝓥 n → 𝓥 (succ n)

     |ℕ₀|   n       = successor.⌜ℕ₀⌝
     |ℕ₁|   n       = successor.⌜ℕ₁⌝
     |ℕ|    n       = successor.⌜ℕ⌝
     _|+|_  m n a b = successor._⌜+⌝_ (Lift-L-max m n a) (Lift-R-max m n b)
     |Σ|    m n a b = successor.⌜Σ⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
     |Π|    m n a b = successor.⌜Π⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
     |W|    m n a b = successor.⌜W⌝   (Lift-L-max m n a) (λ x → Lift-R-max m n (b (Lift-L-max← m n a x)))
     |Id|   n       = successor.⌜Id⌝
     |U|    n       = successor.⌜U⌝
     |T|    n       = successor.⌜T⌝

{-
     |ℕ₀|-eq : (n : ℕ) → 𝓢 n |ℕ₀| ≡₁ ℕ₀
     |ℕ₁|-eq : (n : ℕ) → 𝓢 n |ℕ₁| ≡₁ ℕ₁
     |ℕ|-eq  : (n : ℕ) → 𝓢 n |ℕ|  ≡₁ ℕ
     |+|-eq  : (m n : ℕ) → (a b : 𝓥 n) → 𝓢 n (a |+| b) ≡₁ (𝓢 n a + 𝓢 n b)
     |Σ|-eq  : (m n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Σ| a b) ≡₁ (Σ x ꞉ 𝓢 n a , 𝓢 n (b x))
     |Π|-eq  : (m n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|Π| a b) ≡₁ (Π x ꞉ 𝓢 n a , 𝓢 n (b x))
     |W|-eq  : (n : ℕ) → (a : 𝓥 n) (b : 𝓢 n a → 𝓥 n) → 𝓢 n (|W| a b) ≡₁ (W x ꞉ 𝓢 n a , 𝓢 n (b x))
     |U|-eq : (n : ℕ) → 𝓢 (succ n) (|U| (succ n)) ≡₁ 𝓥 n
     |T|-eq : (n : ℕ) (a : 𝓥 n) → 𝓢 (succ n) (|T| n a) ≡₁ 𝓢 n a

     |ℕ₀|-eq    = refl _
     |ℕ₁|-eq    = refl _
     |ℕ|-eq     = refl _
     |+|-eq a b = refl _
     |Σ|-eq a b = refl _
     |Π|-eq a b = refl _
     |W|-eq a b = refl _
     |U|-eq n   = refl _
     |T|-eq n a = refl _
-}
\end{code}

An ordinal indexed tower of universes:

\begin{code}

 sum : (I : V) → (S I → internal-universe) → internal-universe
 sum I α = (⌜Σ⌝ I (λ u → pr₁ (α u)) , λ {(u , s) → pr₂ (α u) s})

 data Ord : Set where
  zero : Ord
  succ : Ord → Ord
  sup  : (ℕ → Ord) → Ord

 w : Ord → internal-universe
 w zero     = ⌜ℕ₀⌝ , λ ()
 w (succ x) = next (w x)
 w (sup α)  = sum ⌜ℕ⌝ (λ i → w (α i))

\end{code}

I think that now we will lose some definitional equalities, compared
to the ℕ-indexed tower. Leave this for later.
