{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.int where

open import additive-group
open import int


instance
  AdditiveCommMonoid-Int : AdditiveCommMonoid Int
  AdditiveCommMonoid-Int = record
    { comm-monoid = record
      { monoid = record
        { ε = (int 0)
        ; _∙_ = _ℤ+_
        ; ∙-assoc = ℤ+-assoc
        ; ∙-left-ε = ℤ+-left-zero
        ; ∙-right-ε = ℤ+-right-zero
        ; isSet-Domain = isSetInt
        }
      ; ∙-commute = ℤ+-commute
      }
    }

  AdditiveGroup-Int : AdditiveGroup AdditiveCommMonoid-Int
  AdditiveGroup-Int = record
    { -_ = ℤ-_
    ; +-inverse = add-minus-zero
    }
