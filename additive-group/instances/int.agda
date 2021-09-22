{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.int where

open import additive-group
open import base
open import group
open import int using (Int)


instance
  AdditiveCommMonoid-Int : AdditiveCommMonoid Int
  AdditiveCommMonoid-Int = record
    { comm-monoid = record
      { monoid = record
        { ε = (int.int 0)
        ; _∙_ = int._+_
        ; ∙-assoc = \ {m} {n} {o} -> int.+-assoc {m} {n} {o}
        ; ∙-left-ε = int.+-left-zero
        ; ∙-right-ε = int.+-right-zero
        }
      ; ∙-commute = \ {m} {n} -> int.+-commute {m} {n}
      ; isSet-Domain = int.isSetInt
      }
    }

  AdditiveGroup-Int : AdditiveGroup AdditiveCommMonoid-Int
  AdditiveGroup-Int = record
    { -_ = int.-_
    ; +-inverse = \ {n} -> int.add-minus-zero {n}
    }
