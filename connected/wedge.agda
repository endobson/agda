{-# OPTIONS --cubical --safe --exact-split #-}

module connected.wedge where

open import base
open import cubical hiding (glue)
open import nat.arithmetic
open import additive-group
open import additive-group.instances.nat
open import equality-path
open import equality.square
open import hlevel.base
open import functions
open import connected
open import connected.n-type
open import connected.truncated
open import equivalence
open import pushout
open import pointed.base
open import pointed.pushout
open import truncation.generic

module _ {ℓA ℓB ℓP : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) {nA nB : Nat}
  (cA : isConnectedₙ nA A) (cB : isConnectedₙ nB B)
  (P : A -> B -> Type ℓP) (hP : ∀ a b -> isOfHLevel (suc (suc (nA + nB))) (P a b))
  where

  module _ (f : ∀ a -> P a ★B) (g : ∀ b -> P ★A b) (p : f ★A == g ★B) where
    extend-raw-wedge :
      Σ[ h ∈ (∀ a b -> P a b) ]
      Σ[ qa ∈ (∀ a -> h a ★B == f a) ]
      Σ[ qb ∈ (∀ b -> h ★A b == g b) ]
       (p == sym (qa ★A) >=> qb ★B)
    extend-raw-wedge = h , qa , qb , sq₅
      where
      a₀ : Top -> A
      a₀ _ = ★A
      b₀ : Top -> B
      b₀ _ = ★B

      isConnected-a₀ : isConnectedMapₙ₋₂ (suc nA) a₀
      isConnected-a₀ = transport (isConnectedₙ₋₂∙-path (suc nA) A∙) cA
      isConnected-b₀ : isConnectedMapₙ₋₂ (suc nB) b₀
      isConnected-b₀ = transport (isConnectedₙ₋₂∙-path (suc nB) B∙) cB


      Q : A -> Type (ℓ-max ℓB ℓP)
      Q a = fiber (precompose b₀ (P a)) (\_ -> f a)
      hQ : ∀ a -> isOfHLevel (suc nA) (Q a)
      hQ a =
        isConnectedMap->isOfHLevel-precompose {n = suc nB}
          isConnected-b₀ (P a) (hP' a) (\_ -> f a)

        where
        hP' : ∀ a b -> isOfHLevel (suc nA + suc nB) (P a b)
        hP' a b = transport (\i -> isOfHLevel (suc (+'-right-suc {nA} {nB} (~ i))) (P a b))
                            (hP a b)


      Q₀ : Q ★A
      Q₀ = g , \i _ -> p (~ i)

      ctr : isContr (fiber (precompose a₀ Q) (\_ -> Q₀))
      ctr =
        isConnectedMap->isOfHLevel-precompose {n = suc nA} {k = 0}
          isConnected-a₀ Q (hQ) (\_ -> Q₀)

      ctr₀ : (fiber (precompose a₀ Q) (\_ -> Q₀))
      ctr₀ = fst ctr

      hqa : ∀ a -> fiber (precompose b₀ (P a)) (\_ -> f a)
      hqa = fst (fst ctr)

      h : ∀ a b -> P a b
      h a = fst (hqa a)
      qa : ∀ a -> h a ★B == f a
      qa a i = snd (hqa a) i tt

      pq₀ : Path (fiber (precompose b₀ (P ★A)) (\_ -> f ★A))
                 (hqa ★A)
                 (Q₀)
      pq₀ i = snd (fst ctr) i tt

      qb : ∀ b -> Path (P ★A b) (h ★A b) (g b)
      qb b i = fst (pq₀ i) b

      sq : Square (qa ★A) (sym p) (qb ★B) (reflᵉ (f ★A))
      sq i j = snd (pq₀ i) j tt

      sq₂ : Square (reflᵉ (f ★A)) (qb ★B) (sym (qa ★A)) p
      sq₂ j i = snd (pq₀ i) (~ j) tt

      sq₃ : Square (reflᵉ (f ★A)) (qb ★B) (sym (qa ★A)) (refl ∙∙ sym (qa ★A) ∙∙ (qb ★B))
      sq₃ = square-filler _ _ _

      sq₄ : p == (refl ∙∙ sym (qa ★A) ∙∙ (qb ★B))
      sq₄ = transP-sym (symP (▪ᵀ sq₂)) (▪ᵀ sq₃)

      sq₅ : p == (sym (qa ★A) >=> (qb ★B))
      sq₅ = sq₄ >=> (\i -> (\j -> qa ★A (~ (j ∧ i))) ∙∙ (\j -> qa ★A (~ (j ∨ i))) ∙∙ (qb ★B))





module _ {ℓA ℓB ℓP : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) {nA nB : Nat}
  (cA : isConnectedₙ nA A) (cB : isConnectedₙ nB B)
  (P : A -> B -> Type ℓP) (hP : ∀ a b -> isOfHLevel (suc (suc (nA + nB))) (P a b))
  where
  private
    P× : A × B -> Type ℓP
    P× (a , b) = P a b

  module _ (f : (w : Wedge A∙ B∙) -> P× (Wedge->× w)) where
    extend-wedge :
      Σ[ h ∈ (∀ a b -> P a b) ]
      Σ[ qa ∈ (∀ a -> h a ★B == f (inj-l a)) ]
      Σ[ qb ∈ (∀ b -> h ★A b == f (inj-r b)) ]
       ((\i -> f (glue tt i)) == sym (qa ★A) >=> qb ★B)
    extend-wedge = extend-raw-wedge A∙ B∙ cA cB P hP (f ∘ inj-l) (f ∘ inj-r) (\i -> f (glue tt i))
