{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.commutative-monoid where

open import base
open import commutative-monoid
open import order
open import order.minmax

module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{Max : MaxOperationStr LO}}
         {{Min : GlobalMinOperationStr LO}} where

  MaxCommMonoid : CommMonoid D
  MaxCommMonoid = record
    { monoid = record
      { ε = global-min
      ; _∙_ = max
      ; ∙-left-ε = max-≯-path global-min-≮
      ; ∙-right-ε = max-≮-path global-min-≮
      ; ∙-assoc = max-assoc
      }
    ; ∙-commute = max-commute
    ; isSet-Domain = LinearOrderStr.isSet-D LO
    }
