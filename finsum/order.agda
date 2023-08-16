{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.order where

open import additive-group
open import base
open import commutative-monoid
open import commutative-monoid.binary-product
open import commutative-monoid.subtype
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finsum
open import functions
open import order
open import ordered-additive-group
open import relation

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {O : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM O}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      IACM = ACM
      IO = O

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteSum-preserves-0≤ : {f : I -> D} ->
                             (lt : (i : I) -> 0# ≤ f i) ->
                             0# ≤ finiteSum f
    finiteSum-preserves-0≤ {f} lt =
      trans-≤-= (snd (finiteMerge CM-D⁺ f'))
                (sym (finiteMerge-homo-inject CommMonoidʰ-fst))
      where
      D⁺ : Type (ℓ-max ℓD ℓ≤)
      D⁺ = Σ D (0# ≤_)
      f' : (i : I) -> D⁺
      f' i = f i , lt i

      CM-D⁺ : CommMonoid D⁺
      CM-D⁺ = SubCommMonoidStr (\_ -> isProp-≤) CM refl-≤ +-preserves-0≤

    finiteSum-preserves-≤ : {f g : I -> D} ->
                            (lt : (i : I) -> f i ≤ g i) ->
                            finiteSum f ≤ finiteSum g
    finiteSum-preserves-≤ {f} {g} lt =
      subst2 _≤_ (sym (finiteMerge-homo-inject (CommMonoidʰ-proj₁ CM CM) >=> cong proj₁ path))
                 (sym (finiteMerge-homo-inject (CommMonoidʰ-proj₂ CM CM) >=> cong proj₂ path))
                 (snd (finiteMerge CM-2D⁺ fg))
      where
      2D : Type ℓD
      2D = D × D
      2D⁺ : Type (ℓ-max ℓD ℓ≤)
      2D⁺ = Σ[ d ∈ 2D ] (proj₁ d ≤ proj₂ d)

      fg : I -> 2D⁺
      fg i = (f i , g i) , lt i

      CM-2D : CommMonoid 2D
      CM-2D = CommMonoidStr-× CM CM

      CM-2D⁺ : CommMonoid 2D⁺
      CM-2D⁺ = SubCommMonoidStr (\_ -> isProp-≤) CM-2D refl-≤ +-preserves-≤

      path : finiteMerge CM-2D (\i -> f i , g i) ==
             fst (finiteMerge CM-2D⁺ fg)
      path = (finiteMerge-homo-inject CommMonoidʰ-fst)
