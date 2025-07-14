{-# OPTIONS --cubical --safe --exact-split #-}

module connected.truncated where


open import base
open import additive-group
open import additive-group.instances.nat
open import connected.n-type
open import cubical
open import funext
open import functions
open import hlevel.base
open import hlevel.pi
open import hlevel.sigma
open import hlevel.equivalence
open import connected
open import equality-path
open import equivalence
open import isomorphism
open import univalence
open import truncation.generic

module _ {ℓA : Level} {A : Type ℓA} where
  isOfHLevelPath->isOfHLevel : ∀ n -> ((a₁ a₂ : A) -> isOfHLevel n (a₁ == a₂)) -> isOfHLevel (suc n) A
  isOfHLevelPath->isOfHLevel zero h a₁ a₂ = fst (h a₁ a₂)
  isOfHLevelPath->isOfHLevel (suc n) h = h



module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {f : A -> B} where
  opaque
    isConnectedMap->isOfHLevel-precompose : {n k : Nat} {ℓP : Level} ->
      isConnectedMapₙ₋₂ n f -> (P : B -> Type ℓP) -> (∀ b -> isOfHLevel (k + n) (P b)) ->
      ∀ g -> isOfHLevel k (fiber (precompose f P) g)
    isConnectedMap->isOfHLevel-precompose {n} {0} c P hP =
      isEquiv.equiv-proof (isConnectedMap->isEquiv-precompose c P hP)
    isConnectedMap->isOfHLevel-precompose {n} {suc k} {ℓP} c P hP g =
      isOfHLevelPath->isOfHLevel k rec'
      where
      check : fiber (precompose f P) g ==
              (Σ[ h ∈ (∀ b -> P b) ] (precompose f P h == g))
      check = refl


      module _ (x₁@(h₁ , p₁) x₂@(h₂ , p₂) : fiber (precompose f P) g) where

        P' : ∀ B -> Type ℓP
        P' b = Path (P b) (h₁ b) (h₂ b)

        hP' : ∀ b -> isOfHLevel (k + n) (P' b)
        hP' b = isOfHLevelPath' (k + n) (hP b) _ _

        g' : ∀ a -> P' (f a)
        g' a = (\i -> (p₁ i a)) >=> (\i -> (p₂ (~ i) a))

        rec : isOfHLevel k (fiber (precompose f P') g')
        rec = isConnectedMap->isOfHLevel-precompose c P' hP' g'

        eq : (x₁ == x₂) ≃ (fiber (precompose f P') g')
        eq = isoToEquiv (iso for back fb bf)
          where
          path₁ : ∀ (ph : h₁ == h₂) ->
            Square p₁ p₂ (\i -> ph i ∘ f) refl ==
            Square p₁ p₂ (\i -> ph i ∘ f) (refl ∙∙ refl ∙∙ refl)
          path₁ ph i = Square p₁ p₂ (\i -> ph i ∘ f) (∙∙-refl (~ i))

          path₂ : ∀ (ph : h₁ == h₂) ->
            Square p₁ p₂ (\i -> ph i ∘ f) (reflᵉ g ∙∙ reflᵉ g ∙∙ reflᵉ g) ==
            Square refl refl (\i -> ph i ∘ f) (p₁ ∙∙ reflᵉ g ∙∙ sym p₂)
          path₂ ph i =
            Square (\j -> p₁ (j ∧ ~ i)) (\j -> p₂ (j ∧ ~ i))
                   (\i -> ph i ∘ f)
                   ((\j -> p₁ (j ∨ ~ i)) ∙∙ reflᵉ g ∙∙ (\j -> p₂ (~ j ∨ ~ i)))

          for : (x₁ == x₂) -> (fiber (precompose f P') g')
          for px = (\b i -> ph i b) , (\j a i -> step₂ i j a)
            where
            ph = cong fst px
            pp = cong snd px

            step₂ : Square refl refl (\i -> ph i ∘ f) (p₁ ∙∙ reflᵉ g ∙∙ sym p₂)
            step₂ = transport (path₁ ph >=> path₂ ph) pp

          back : (fiber (precompose f P') g') -> (x₁ == x₂)
          back (ph' , pp') = \i -> ph i , pp i
            where
            ph : h₁ == h₂
            ph i b = ph' b i

            pp : PathP (\i -> ph i ∘ f == g) p₁ p₂
            pp = transport (sym (path₁ ph >=> path₂ ph)) (\i j (a : A) -> pp' j a i)

          fb : ∀ x -> for (back x) == x
          fb (ph' , pp') k =
            ph' ,
            \j a i -> transport-sym (sym (path₁ ph >=> path₂ ph)) (\i j a -> pp' j a i) k i j a
            where
            ph : h₁ == h₂
            ph i b = ph' b i

          bf : ∀ x -> back (for x) == x
          bf px k =
            \i -> ph i ,
                  transport-sym (path₁ ph >=> path₂ ph) pp k i
            where
            ph = cong fst px
            pp = cong snd px



        rec' : isOfHLevel k (x₁ == x₂)
        rec' = ≃-isOfHLevel (equiv⁻¹ eq) k rec
