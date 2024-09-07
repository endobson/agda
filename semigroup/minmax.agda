{-# OPTIONS --cubical --safe --exact-split #-}

module semigroup.minmax where

open import base
open import order
open import order.minmax
open import relation
open import semigroup

module _ {ℓD ℓ< : Level} (D : Type ℓD) {_<_ : Rel D ℓ<} {LO : isLinearOrder _<_} where
  module _ {{MS : MinOperationStr LO}} where
    CommutativeSemigroupStr-Min : CommutativeSemigroupStr D
    CommutativeSemigroupStr-Min = record
      { _∙_ = min
      ; ∙-assoc = min-assoc
      ; ∙-commute = min-commute
      ; isSet-Domain = isLinearOrder.isSet-D LO
      }

  module _ {{MS : MaxOperationStr LO}} where
    CommutativeSemigroupStr-Max : CommutativeSemigroupStr D
    CommutativeSemigroupStr-Max = record
      { _∙_ = max
      ; ∙-assoc = max-assoc
      ; ∙-commute = max-commute
      ; isSet-Domain = isLinearOrder.isSet-D LO
      }
