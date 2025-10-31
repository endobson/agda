{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.instances.int where

open import apartness
open import apartness.decidable
open import apartness.instances.int
open import base
open import equality-path
open import funext
open import int.base
open import int.cover
open import integral-domain
open import integral-domain.apart-linear-order
open import order
open import order.instances.int
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.instances.int
open import relation
open import ring.implementations.int
open import sigma.base
open import sum
open import univalence

private
  TA-ℤ<> : isTightApartness _<>_
  TA-ℤ<> = isLinearOrder->isTightApartness-<> useⁱ

  ℤ!= : Rel ℤ ℓ-zero
  ℤ!= = _!=_

  IntegralDomain-ℤ<> : IntegralDomain IntRing TA-ℤ<>
  IntegralDomain-ℤ<> = IntegralDomain-LinearOrderStr IntRing _ 0<1

opaque
  instance
    IntegralDomain-ℤ : IntegralDomain IntRing isTightApartness-ℤ#
    IntegralDomain-ℤ = subst ID path IntegralDomain-ℤ<>
      where
      T : Type ℓ-one
      T = Σ[ R ∈ Rel ℤ ℓ-zero ] (isTightApartness R)

      ID : T -> Type ℓ-one
      ID (R , isTA) = IntegralDomain IntRing isTA

      decide-!= : Decidable2 ℤ!=
      decide-!= a b = case (discreteInt a b) of
        \{ (yes a=b) -> (no (\a!=b -> a!=b a=b))
         ; (no a!=b) -> (yes a!=b)
         }

      decide-<> : Decidable2 _<>_
      decide-<> a b = case (trichotomous-< a b) of
        \{ (tri< a<b _ _) -> yes (inj-l a<b)
         ; (tri= a≮b _ b≮a) -> no (either a≮b b≮a)
         ; (tri> _ _ b<a) -> yes (inj-r b<a)
         }

      R-path : _<>_ == ℤ!=
      R-path = funExt2 (\a b ->
        (ua (DecidableApartness-equiv TA-ℤ<> isTightApartness-ℤ# decide-<> decide-!= a b)))

      path : Path T (_<>_ , TA-ℤ<>) (ℤ!= , isTightApartness-ℤ#)
      path = ΣProp-path (isProp-isTightApartnessOfSet isSetInt) R-path
