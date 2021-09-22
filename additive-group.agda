{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group where

open import base
open import equality
open import commutative-monoid
open import group
open import hlevel

record AdditiveCommMonoid {ℓ : Level} (D : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    comm-monoid : CommMonoid D

  isSet-Domain : isSet D
  isSet-Domain = CommMonoid.isSet-Domain comm-monoid

module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  private
    module CM = CommMonoid (AdditiveCommMonoid.comm-monoid ACM)
  infixl 6 _+_

  _+_ : D -> D -> D
  _+_ = CM._∙_

  0# : D
  0# = CM.ε

  abstract
    +-assoc : {m n o : D} -> (m + n) + o == m + (n + o)
    +-assoc = CM.∙-assoc

    +-left-zero : {m : D} -> (0# + m) == m
    +-left-zero = CM.∙-left-ε

    +-right-zero : {m : D} -> (m + 0#) == m
    +-right-zero = CM.∙-right-ε

    +-commute : {m n : D} -> (m + n) == (n + m)
    +-commute = CM.∙-commute


module _ {ℓ : Level} {D : Type ℓ} (ACM : AdditiveCommMonoid D) where
  private
    instance
      IACM = ACM

  record AdditiveGroup  : Type ℓ where
    no-eta-equality
    field
      -_ : D -> D
      +-inverse : {x : D} -> x + (- x) == 0#

    group-str : GroupStr D
    group-str .GroupStr.comm-monoid = AdditiveCommMonoid.comm-monoid ACM
    group-str .GroupStr.inverse = -_
    group-str .GroupStr.∙-left-inverse = +-commute >=> +-inverse

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} where
  open AdditiveGroup AG public using (-_)
  private
    module AG = AdditiveGroup AG

    instance
      IACM = ACM

  abstract
    +-inverse : {x : D} -> x + (- x) == 0#
    +-inverse = AG.+-inverse
