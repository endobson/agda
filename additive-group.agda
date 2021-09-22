{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group where

open import base
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


record AdditiveGroup {ℓ : Level} (D : Type ℓ) {{ACM : AdditiveCommMonoid D}} : Type ℓ where
  no-eta-equality
  field
    -_ : D -> D
    +-inverse : {x : D} -> x + (- x) == 0#

-- TODO expose this once it is ready to replace Ring
-- module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} {{AG : AdditiveGroup D}} where
--   open AdditiveGroup AG public
