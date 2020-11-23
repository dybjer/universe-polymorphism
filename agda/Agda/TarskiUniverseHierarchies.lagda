Various hierarchies of universes.

This file is an index of various Agda files.

\begin{code}

module TarskiUniverseHierarchies where

import MLTT
import InconsistentUniverse
import NonPositiveCumulativeByCoercion
import NonPositiveCumulativeOnTheNose
import Palmgren
import SequenceOfUniversesBase
import SequenceOfUniversesV1
import SequenceOfUniversesV2
import UniversesStructures
import OrdinalIndexedUniverses


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

 ⌜×⌝ :  (i j : L) → U i → U j → U (i ⊔ j)
 ⌜×⌝ i j a b = ⌜Σ⌝ i j a (λ _ → b)

 Lift : (i j : L) → U i → U (i ⊔ j)
 Lift i j a = ⌜×⌝ i j a (⌜ℕ₁⌝ j)

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
