{-# OPTIONS --cubical --safe --exact-split #-}

module semidomain.apart-linear-order where

open import additive-group
open import apartness
open import base
open import semidomain
open import order
open import ordered-semiring
open import relation
open import semiring

module _ {ℓ ℓ< : Level} {D : Type ℓ} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO
      TA = isLinearOrder->isTightApartness-<> LO

  -- We only have semidomains for non trivial rings
  Semidomain-LinearOrderStr : (0# < 1#) -> Semidomain S TA
  Semidomain-LinearOrderStr 0<1 = record
    { 1#0 = inj-r 0<1
    ; StronglyInjective-*₁ = StronglyInjective-D*₁
    ; StronglyExtensional-*₁ = StronglyExtensional-D*₁
    }
    where
    StronglyInjective-D*₁ : (a : D) -> (a # 0#) -> StronglyInjective (a *_)
    StronglyInjective-D*₁ a (inj-l a<0) {b} {c} (inj-l b<c) =
      inj-r (*₁-flips-< a<0 b<c)
    StronglyInjective-D*₁ a (inj-l a<0) {b} {c} (inj-r c<b) =
      inj-l (*₁-flips-< a<0 c<b)
    StronglyInjective-D*₁ a (inj-r 0<a) {b} {c} (inj-l b<c) =
      inj-l (*₁-preserves-< 0<a b<c)
    StronglyInjective-D*₁ a (inj-r 0<a) {b} {c} (inj-r c<b) =
      inj-r (*₁-preserves-< 0<a c<b)

    StronglyExtensional-D*₁ : (a : D) -> StronglyExtensional (a *_)
    StronglyExtensional-D*₁ a {b} {c} (inj-l ab<ac) =
      case (*₁-fully-reflects-< ab<ac) of
        (\{ (inj-l (b<c , 0<a)) -> inj-l b<c
          ; (inj-r (c<b , a<0)) -> inj-r c<b
          })
    StronglyExtensional-D*₁ a {b} {c} (inj-r ac<ab) =
      case (*₁-fully-reflects-< ac<ab) of
        (\{ (inj-l (c<b , 0<a)) -> inj-r c<b
          ; (inj-r (b<c , a<0)) -> inj-l b<c
          })
