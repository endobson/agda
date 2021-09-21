{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.reader where

open import additive-group
open import base
open import funext
open import group
open import hlevel


module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  instance
    AdditiveCommMonoid-Reader : {ℓ₂ : Level} {A : Type ℓ₂} -> AdditiveCommMonoid (A -> D)
    AdditiveCommMonoid-Reader = record
      { comm-monoid = record
        { monoid = record
          { ε = \_ -> 0#
          ; _∙_ = \f g i -> (f i) + (g i)
          ; ∙-assoc = funExt (\_ -> +-assoc)
          ; ∙-left-ε = funExt (\_ -> +-left-zero)
          ; ∙-right-ε = funExt (\_ -> +-right-zero)
          }
        ; ∙-commute = funExt (\_ -> +-commute)
        ; isSet-Domain = isSetΠ (\_ -> AdditiveCommMonoid.isSet-Domain ACM)
        }
      }


module _ {ℓ : Level} {D : Type ℓ}
         {{ACM : AdditiveCommMonoid D}}
         {{AG : AdditiveGroup D}}
         where
  instance
    AdditiveGroup-Reader : {ℓ₂ : Level} {A : Type ℓ₂} -> AdditiveGroup (A -> D)
    AdditiveGroup-Reader = record
      { -_ = \f i -> - (f i)
      ; +-inverse = funExt (\_ -> +-inverse)
      }
