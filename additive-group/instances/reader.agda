{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.reader where

open import additive-group
open import base
open import funext
open import hlevel


module _ {ℓ : Level} {D : Type ℓ} (ACM : AdditiveCommMonoid D) where
  private
    instance
      IACM = ACM

  AdditiveCommMonoid-Reader : {ℓ₂ : Level} (A : Type ℓ₂) -> AdditiveCommMonoid (A -> D)
  AdditiveCommMonoid-Reader _ = record
    { comm-monoid = record
      { monoid = record
        { ε = \_ -> 0#
        ; _∙_ = \f g i -> (f i) + (g i)
        ; ∙-assoc = funExt (\_ -> +-assoc)
        ; ∙-left-ε = funExt (\_ -> +-left-zero)
        ; ∙-right-ε = funExt (\_ -> +-right-zero)
        ; isSet-Domain = isSetΠ (\_ -> AdditiveCommMonoid.isSet-Domain ACM)
        }
      ; ∙-commute = funExt (\_ -> +-commute)
      }
    }


module _ {ℓ : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D}
         (AG : AdditiveGroup ACM)
         {ℓ₂ : Level} (A : Type ℓ₂)
         where
  private
    instance
      IACM-Reader = AdditiveCommMonoid-Reader ACM A

    module AG = AdditiveGroup AG

  AdditiveGroup-Reader : AdditiveGroup IACM-Reader
  AdditiveGroup-Reader = record
    { -_ = \f i -> AG.- (f i)
    ; +-inverse = funExt (\_ -> AG.+-inverse)
    }
