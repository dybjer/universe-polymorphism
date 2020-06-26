24th June 2020. Version of 25th June 2020.

Bezem-Coquand-Dybjer-Escardo discussion (or BCDE discussion) on
universe lifting and "completeness" of our non-cumulative type theory
with universe polymorphism in the sense of definability.

  * Universe lifting preserves the type formers.

  * Given the other data for our type theory, universe lifting is
    available if and only if every universe has some type (it doesn't
    matter what this type is).

  * It is possible to define a type of every universe in our type
    theory without lifting, but only schematically: we need a
    different definition for each universe, and the quantification is
    external (for the initial model).

    There doesn't seem to be a uniform way to do this internally in
    our type theory.

(Remark added 25th June. There is nothing special about the type
formers being preserved by universe lifting. This is just an instance
of the fact that they are preserved by equivalences. However, the
preservation of Π by Lift holds without function extensionality using
the fact that (lift,down) form a definitional isomorphism (they
compose to the identity definitionally), but the general preservation
by equivalences seems to require function extensionality. The
preservation of identity types requires an additional axioms, it
seems: we can do with K (and so with equality reflection) and with
univalence.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

"--safe" means that no postulates are used.

"--exact-split" means that definitions by pattern matching are
accepted only if they can be translated to case trees using
eliminators.

\begin{code}


module BCDE-discussion where

open import HoTT-UF-Agda

variable
 𝓤' 𝓥' 𝓦' 𝓣' : Universe

Π-preservation : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
               → Lift 𝓦 (Π A) ≃ (Π l ꞉ Lift 𝓣 X , Lift 𝓣 (A (lower l)))
Π-preservation {𝓤} {𝓥} {𝓦} {𝓣} X A =
  invertibility-gives-≃ φ (γ , η , ε)
 where
  φ : Lift 𝓦 (Π A) → (Π l ꞉ Lift 𝓣 X , Lift 𝓣 (A (lower l)))
  φ f (lift x) = lift (lower f x)
  γ : codomain φ → domain φ
  γ g = lift (λ x → lower (g (lift x)))
  η : γ ∘ φ ∼ id
  η = refl
  ε : φ ∘ γ ∼ id
  ε = refl

Π-preservation' : global-dfunext
                → (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                  (X' : 𝓤' ̇ ) (A' : X' → 𝓦 ̇ )
                  (f : X → X')
                  (g : (x : X) → A x → A' (f x))
                → is-equiv f
                → ((x : X) → is-equiv (g x))
                → Π A ≃ Π A'
Π-preservation' fe X A X' A' f g i j = γ
 where
  a : (Π x' ꞉ X' , A' x') ≃ (Π x ꞉ X , A' (f x))
  a = Π-change-of-variable fe fe A' f i

  γ = (Π x ꞉ X , A x)      ≃⟨ Π-cong fe fe (λ x → g x , j x) ⟩
      (Π x ꞉ X , A' (f x)) ≃⟨ ≃-sym a                        ⟩
      (Π x' ꞉ X' , A' x')  ■


Π-Lift-preservation : global-dfunext
                    → (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                    → Π A ≃ (Π l ꞉ Lift 𝓦 X , A (lower l))
Π-Lift-preservation {𝓤} {𝓥} {𝓦} fe X A = Π-preservation' fe X A
                                           (Lift 𝓦 X) (λ l → A (lower l))
                                           lift
                                           g
                                           (invertibles-are-equivs lift
                                             (lower , lower-lift {𝓤} {𝓦} , lift-lower))
                                           j

 where
  g : (x : X) → A x → A (lower {𝓤} {𝓦} (lift x))
  g x = id
  j : (x : X) → is-equiv (g x)
  j x = id-is-equiv (A x)


Π-preservation-again : global-dfunext
                     → (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                     → Lift 𝓦 (Π A)
                     ≃ (Π l ꞉ Lift 𝓣 X , Lift 𝓣' (A (lower l)))
Π-preservation-again {𝓤} {𝓥} {𝓦} {𝓣} {𝓣'} fe X A =

  Lift 𝓦 (Π A)                            ≃⟨ Lift-≃ (Π A)                               ⟩
  Π A                                      ≃⟨ Π-Lift-preservation fe X A                ⟩
  (Π l ꞉ Lift 𝓣 X , A (lower l))           ≃⟨ Π-cong fe fe (λ x → ≃-Lift (A (lower x))) ⟩
  (Π l ꞉ Lift 𝓣 X , Lift 𝓣' (A (lower l))) ■

\end{code}

We repeat the development for Σ:

\begin{code}
Σ-preservation : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
               → Lift 𝓦 (Σ A)
               ≃ (Σ l ꞉ Lift 𝓣 X , Lift 𝓣 (A (lower l)))
Σ-preservation {𝓤} {𝓥} {𝓦} {𝓣} X A =
  invertibility-gives-≃ φ (γ , η , ε)
 where
  φ : Lift 𝓦 (Σ A)
    → (Σ l ꞉ Lift 𝓣 X , Lift 𝓣 (A (lower l)))
  φ (lift (x , a)) = lift x , lift a
  γ : codomain φ → domain φ
  γ (lift x , lift a) = lift (x , a)
  η : γ ∘ φ ∼ id
  η = refl
  ε : φ ∘ γ ∼ id
  ε = refl

\end{code}

The following proofs are essentially the same as those for Π above:

\begin{code}

Σ-preservation' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                  (X' : 𝓤' ̇ ) (A' : X' → 𝓦 ̇ )
                  (f : X → X')
                  (g : (x : X) → A x → A' (f x))
                → is-equiv f
                → ((x : X) → is-equiv (g x))
                → Σ A ≃ Σ A'
Σ-preservation' X A X' A' f g i j = γ
 where
  a : (Σ x' ꞉ X' , A' x') ≃ (Σ x ꞉ X , A' (f x))
  a = Σ-change-of-variable A' f i

  γ = (Σ x ꞉ X , A x)      ≃⟨ Σ-cong (λ x → g x , j x) ⟩
      (Σ x ꞉ X , A' (f x)) ≃⟨ ≃-sym a                  ⟩
      (Σ x' ꞉ X' , A' x')  ■

Σ-Lift-preservation : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                    → Σ A ≃ (Σ l ꞉ Lift 𝓦 X , A (lower l))
Σ-Lift-preservation {𝓤} {𝓥} {𝓦} X A = Σ-preservation' X A
                                         (Lift 𝓦 X) (λ l → A (lower l))
                                         lift
                                         g
                                         (invertibles-are-equivs lift
                                           (lower , lower-lift {𝓤} {𝓦} , lift-lower))
                                         j

 where
  g : (x : X) → A x → A (lower {𝓤} {𝓦} (lift x))
  g x = id
  j : (x : X) → is-equiv (g x)
  j x = id-is-equiv (A x)

Σ-preservation-again : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
               → Lift 𝓦 (Σ A)
               ≃ (Σ l ꞉ Lift 𝓣 X , Lift 𝓣' (A (lower l)))
Σ-preservation-again {𝓤} {𝓥} {𝓦} {𝓣} {𝓣'} X A =

  Lift 𝓦 (Σ A)                            ≃⟨ Lift-≃ (Σ A)                         ⟩
  Σ A                                      ≃⟨ Σ-Lift-preservation X A             ⟩
  (Σ l ꞉ Lift 𝓣 X , A (lower l))           ≃⟨ Σ-cong (λ x → ≃-Lift (A (lower x))) ⟩
  (Σ l ꞉ Lift 𝓣 X , Lift 𝓣' (A (lower l))) ■

\end{code}

The above is not the end of the story: we need to show that the
liftings of Π and Σ satisfy the required "universal properties".

We do this for ℕ now:

\begin{code}

module _ (𝓥 : Universe) where
 ℕ' : 𝓥 ̇
 ℕ' = Lift 𝓥 ℕ

 O' : ℕ'
 O' = lift 0

 succ' : ℕ' → ℕ'
 succ' (lift n) = lift (succ n)

 Lifted-ℕ-induction : (A : ℕ' → 𝓤 ̇ )
                    → A O'
                    → ((n : ℕ') → A n → A (succ' n))
                    → (n : ℕ') → A n

 Lifted-ℕ-induction A a₀ f = Lift-induction 𝓥 ℕ A (ℕ-induction (A ∘ lift) a₀ (λ n → f (lift n)))

\end{code}

Now: does every universe have an empty type, given that we only
postulated an empty type for the first universe 𝓤₀?

The second universe does:

\begin{code}

Zero₁ : 𝓤₁ ̇
Zero₁ = 𝓤₀ ̇ → 𝟘

Zero₁-induction : (A : Zero₁ → 𝓥 ̇ ) → (x : Zero₁) → A x
Zero₁-induction A x = !𝟘 (A x) (x 𝟘)

\end{code}

More generally, successor universes do:

\begin{code}

Zero⁺ : 𝓤 ⁺ ̇
Zero⁺ {𝓤} = 𝓤 ̇ → 𝟘

Zero⁺-induction : (A : Zero⁺ → 𝓥 ̇ ) → (x : Zero⁺) → A x
Zero⁺-induction A x = 𝟘-induction (λ _ → A x) (x 𝟘)

\end{code}

But we don't have induction or case distinction on universe( level)s,
and so we can't turn the above constructions into a uniform (or
polymorphic) definition of an empty type for every universe.

Similarly, every universe has some type: for 𝓤₀ we can choose e.g. the empty
type, and for 𝓤 ⁺ we can choose 𝓤. But such a case distinction is not
available in our type theory.

Using lifting, we can show that every universe has some type in a
uniform way. But we will work with the hypothetical existence of
universe lifting, rather than a concrete construction, in order to
prove some "interdefinability" results.

We use a record type to express the hypothetical existence of universe
lifting, where "up" corresponds to "lift":

\begin{code}

record universe-lifting-is-available : 𝓤ω where
 field
  Up : ∀ {𝓤} 𝓥 → 𝓤 ̇ →  𝓤 ⊔ 𝓥 ̇
  up : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → X → Up 𝓥 X
  Up-induction : ∀ {𝓤} 𝓥
                 {X : 𝓤 ̇ }
                 (A : Up 𝓥 X → 𝓦 ̇ )
               → ((x : X) → A (up x))
               → (u : Up 𝓥 X) → A u
  Up-induction-identity :
                 ∀ {𝓤} 𝓥
                 {X : 𝓤 ̇ }
                 {A : Up 𝓥 X → 𝓦 ̇ }
                 (φ : (x : X) → A (up x))
                 (x : X)
               → Up-induction 𝓥 A φ (up x) ≡ φ x
\end{code}

BTW, Up 𝓥 is an idempotent monad, with up as its unit. The
mutiplication is

\begin{code}

 μ : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → Up 𝓥 (Up 𝓥 X) → Up 𝓥 X
 μ {𝓤} {𝓥} {X} = Up-induction 𝓥 (λ _ → Up 𝓥 X) id
\end{code}

We also define:

\begin{code}

every-universe-has-some-type : 𝓤ω
every-universe-has-some-type = (𝓤 : Universe) → 𝓤 ̇

every-universe-has-a-pointed-type : 𝓤ω
every-universe-has-a-pointed-type = (𝓤 : Universe) → Σ X ꞉ 𝓤 ̇ , X

record every-universe-has-an-empty-type : 𝓤ω where
 field
  O : (𝓤 : Universe) → 𝓤 ̇
  O-induction : (𝓤 𝓥 : Universe) (A : O 𝓤 → 𝓥 ̇ ) (x : O 𝓤) → A x

\end{code}

The above four notions are related as follows:

\begin{code}

claim₀ : universe-lifting-is-available → every-universe-has-some-type
claim₀ l 𝓤 = Up 𝓤 𝟘
 where
  open universe-lifting-is-available l

claim₁ : every-universe-has-a-pointed-type → every-universe-has-some-type
claim₁ φ 𝓤 = pr₁ (φ 𝓤)

claim₂ : every-universe-has-a-pointed-type → every-universe-has-an-empty-type
claim₂ φ = record {
                  O = λ 𝓤 → pr₁ (φ 𝓤) → 𝟘 ;
                  O-induction = λ 𝓤 𝓥 A x → 𝟘-induction (λ _ → A x) (x (pr₂ (φ 𝓤)))
                  }

claim₃ : every-universe-has-some-type → every-universe-has-a-pointed-type
claim₃ e 𝓤 = (e 𝓤 → e 𝓤) , id

claim₄ : every-universe-has-some-type → every-universe-has-an-empty-type
claim₄ e = claim₂ (claim₃ e)

claim₅ : every-universe-has-some-type → universe-lifting-is-available
claim₅ e = record
             {
             Up = Up' ;
             up = up' ;
             Up-induction = Up-induction' ;
             Up-induction-identity = Up-induction-identity'
             }
 where
  a : every-universe-has-an-empty-type
  a = claim₄ e

  open every-universe-has-an-empty-type a

  Up' : ∀ {𝓤} 𝓥 → 𝓤 ̇ →  𝓤 ⊔ 𝓥 ̇
  Up' 𝓥 X = X + O 𝓥
  up' : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → X → Up' 𝓥 X
  up' = inl
  Up-induction' : ∀ {𝓤} 𝓥
                  {X : 𝓤 ̇ }
                  (A : Up' 𝓥 X → 𝓦 ̇ )
                → ((x : X) → A (up' x))
                → (l : Up' 𝓥 X) → A l
  Up-induction' {𝓤} 𝓥 A φ (inl x) = φ x
  Up-induction' {𝓤} 𝓥 A φ (inr x) = O-induction 𝓥 𝓤 (λ _ → A (inr x)) x
  Up-induction-identity' :
                  ∀ {𝓤} 𝓥
                  {X : 𝓤 ̇ }
                  {A : Up' 𝓥 X → 𝓦 ̇ }
                  (φ : (x : X) → A (up' x))
                  (x : X)
                → Up-induction' 𝓥 A φ (up' x) ≡ φ x
  Up-induction-identity' 𝓥 φ x = refl (φ x)
\end{code}

Notice that the induction identity holds definitionally.

So the conclusion is that universe lifting is available if and only if
every universe has some type.

But it doesn't seem to be possible to prove that every universe has
some type in our type theory with non-cumulative universe
polymorphism. The most natural ways to fix this are (1) include an
empty type in each universe or (2) add universe lifting to the
system. The fixes (1) and (2) are equivalent in the sense that (1) and
(2) are interdefinable.

Can we repeat Π-preservation₂ with a hypothetical universe lifting?

\begin{code}

module hypothetical-universe-lifting
        (α : universe-lifting-is-available)
       where
\end{code}

We first derive some general consequences of the hypothesis:

\begin{code}
 open universe-lifting-is-available α

 Up-recursion : ∀ {𝓤} 𝓥
                {X : 𝓤 ̇ }
                {A : 𝓦 ̇ }
              → (X → A)
              → Up 𝓥 X → A
 Up-recursion 𝓥 {X} {A} = Up-induction 𝓥 (λ _ → A)

 Up-recursion-identity : ∀ {𝓤} 𝓥
                         {X : 𝓤 ̇ }
                         {A : 𝓦 ̇ }
                         (φ : X → A)
                         (x : X)
                       → Up-recursion 𝓥 φ (up x) ≡ φ x
 Up-recursion-identity 𝓥 {X} {A} = Up-induction-identity 𝓥 {X} {λ _ → A}

 down : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → Up 𝓥 X → X
 down {𝓤} {𝓥} {X} = Up-recursion 𝓥 id

 down-up : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } (x : X) → down (up x) ≡ x
 down-up 𝓥 = Up-recursion-identity 𝓥 id

 up-down : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } (u : Up 𝓥 X) → up (down u) ≡ u
 up-down {𝓤} 𝓥 {X} = Up-induction 𝓥 A φ
  where
   A : (u : Up 𝓥 X) → 𝓤 ⊔ 𝓥 ̇
   A u = up (down u) ≡ u

   φ : (x : X) → up (down (up x)) ≡ up x
   φ x = ap up (down-up 𝓥 x)

   that-is : (x : X) → A (up x)
   that-is = φ

 up-is-equiv : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → is-equiv (up {𝓤} {𝓥} {X})
 up-is-equiv {𝓤} {𝓥} = invertibles-are-equivs up (down , down-up 𝓥 , up-down 𝓥)

 down-is-equiv : ∀ {𝓤} {𝓥} {X : 𝓤 ̇ } → is-equiv (down {𝓤} {𝓥} {X})
 down-is-equiv {𝓤} {𝓥} = invertibles-are-equivs down (up , up-down 𝓥 , down-up 𝓥)

 Up-equivalence : ∀ {𝓤} {𝓥} (X : 𝓤 ̇ ) → Up 𝓥 X ≃ X
 Up-equivalence X = down , down-is-equiv

\end{code}

Assuming univalence, this implies that Up {𝓤} 𝓥 is an embedding. The
proof of this uses universe-embedding-criterion from the repository
TypeTopology, which is not available in the lecture notes code
HoTT-UF-Agda, which is what we are using here. This further implies
that (Up 𝓥 X ≡ Up 𝓥 Y) ≃ (X ≡ Y) by a general property of embeddings.

\begin{code}
{-
 Π-preservation-again : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
            → Up 𝓦 (Π A)
            ≃ (Π l ꞉ Up 𝓣 X , Up 𝓣 (A (down l)))
 Π-preservation-again {𝓤} {𝓥} {𝓦} {𝓣} X A = invertibility-gives-≃ φ (γ , η , ε)
  where
   φ' : Π A → Π l ꞉ Up 𝓣 X , Up 𝓣 (A (down l))
   φ' f = Up-induction 𝓣 (λ l → Up 𝓣 (A (down l))) (λ x → up (f (down (up x))))

   φ : Up 𝓦 (Π A) → Π l ꞉ Up 𝓣 X , Up 𝓣 (A (down l))
   φ = Up-recursion 𝓦 φ'
   γ : codomain φ → domain φ
   γ g = up h
    where
     k : (x : X) → A (down (up x))
     k x = down (g (up x))
     h : (x : X) → A x
     h x = transport A (down-up 𝓣 x) (k x)
   η : γ ∘ φ ∼ id
   η = Up-induction 𝓦 (λ u → γ (φ u) ≡ u) a
    where
     a : (f : Π A) → γ (Up-recursion 𝓦 φ' (up f)) ≡ up f
     a = {!!}
   ε : φ ∘ γ ∼ id
   ε = {!!}
-}

\end{code}

TODO. Show that λ X x y → Id (Up 𝓥 X) (up x) (up y) is an identity type.
TODO. Show that the lifting of Π, Σ and + (can be suitably defined and) satisfy the defining conditions of Π, Σ and +.

Etc.
