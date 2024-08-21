{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.without-point where

open import base
open import commutative-monoid
open import discrete
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.instances
open import finset.without-point
open import relation
open import without-point

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    private
      instance
        DI : Discrete' I
        DI .Discrete'.f = isFinSet->Discrete (FinSetStr.isFin FI)

    opaque
      finiteMerge-WithoutPoint : (i : I) (f : I -> D) ->
         finiteMerge CM f == f i ∙ finiteMerge CM (\ ((i2 , _) : WithoutPoint I i) -> f i2)
      finiteMerge-WithoutPoint i f =
         finiteMerge-convert CM (MaybeWithoutPoint-eq I i) f >=>
         finiteMerge-Maybe CM _
