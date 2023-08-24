{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.same-fibers where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import finite-commutative-monoid
open import finset
open import isomorphism
open import sigma
open import funext
open import type-algebra

private
  module _ {ℓD ℓS : Level} {D : Type ℓD} (CM : CommMonoid D) (fS : FinSet ℓS) where
    open CommMonoid CM
    private
      ℓSD : Level
      ℓSD = (ℓ-max ℓS ℓD)
      S : Type ℓS
      S = ⟨ fS ⟩



    module _ (f : (S -> D)) where
      private
        PreImage : D -> Type ℓSD
        PreImage d = fiber f d

        ΣPreImage : Type ℓSD
        ΣPreImage = Σ D PreImage

        eval : ΣPreImage -> D
        eval = fst

        ΣPreImage-eq : ΣPreImage ≃ S
        ΣPreImage-eq =
          Σ-swap-eq >eq>
          equiv⁻¹ (Σ-isContr-eq (\s -> isContr-singleton (f s)))

      FinSet-ΣPreImage : FinSet ℓSD
      FinSet-ΣPreImage = ΣPreImage , isFinSet-equiv (equiv⁻¹ ΣPreImage-eq) (snd fS)

      finiteMergeᵉ-fiber : D
      finiteMergeᵉ-fiber = finiteMergeᵉ CM FinSet-ΣPreImage eval


      finiteMergeᵉ-fiber-path : finiteMergeᵉ CM fS f == finiteMergeᵉ-fiber
      finiteMergeᵉ-fiber-path =
        finiteMergeᵉ-convert CM fS FinSet-ΣPreImage ΣPreImage-eq f >=>
        cong (finiteMergeᵉ CM FinSet-ΣPreImage) (funExt path)
        where
        path : (p : ΣPreImage) -> f (fst (snd p)) == fst p
        path (_ , (_ , p)) = p


  module _ {ℓD ℓS₁ ℓS₂ : Level} {D : Type ℓD} (CM : CommMonoid D)
    (fS₁ : FinSet ℓS₁) (fS₂ : FinSet ℓS₂) where
    open CommMonoid CM
    private
      S₁ : Type ℓS₁
      S₁ = ⟨ fS₁ ⟩
      S₂ : Type ℓS₂
      S₂ = ⟨ fS₂ ⟩

    module _ (f : (S₁ -> D)) (g : (S₂ -> D)) where
      module _ (same-fibers : (d : D) -> fiber f d ≃ fiber g d) where
        same-value : finiteMergeᵉ-fiber CM fS₁ f == finiteMergeᵉ-fiber CM fS₂ g
        same-value =
          finiteMergeᵉ-convert CM (FinSet-ΣPreImage CM fS₁ f) (FinSet-ΣPreImage CM fS₂ g) same-Σ fst
          where
          same-Σ : Σ D (fiber g) ≃ Σ D (fiber f)
          same-Σ = equiv⁻¹ (existential-eq same-fibers)


module _
  {ℓD ℓS₁ ℓS₂ : Level} {D : Type ℓD}
  (CM : CommMonoid D)
  (fS₁ : FinSet ℓS₁) (fS₂ : FinSet ℓS₂)
  (f : (⟨ fS₁ ⟩ -> D)) (g : (⟨ fS₂ ⟩ -> D)) where
  finiteMergeᵉ-sameFibers :
    ((d : D) -> fiber f d ≃ fiber g d) ->
    finiteMergeᵉ CM fS₁ f == finiteMergeᵉ CM fS₂ g
  finiteMergeᵉ-sameFibers same =
    finiteMergeᵉ-fiber-path CM fS₁ f >=>
    same-value CM fS₁ fS₂ f g same >=>
    sym (finiteMergeᵉ-fiber-path CM fS₂ g)
