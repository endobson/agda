{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.real where

open import additive-group
open import equality
open import real
open import real.rational
open import real.arithmetic


instance
  AdditiveCommMonoid-ℝ : AdditiveCommMonoid ℝ
  AdditiveCommMonoid-ℝ = record
    { comm-monoid = record
      { monoid = record
        { ε = 0ℝ
        ; _∙_ = _ℝ+_
        ; ∙-assoc = \ {x} {y} {z} -> ℝ+-assoc x y z
        ; ∙-left-ε = \ {x} -> ℝ+-left-zero x
        ; ∙-right-ε = \ {x} -> ℝ+-commute x 0ℝ >=> ℝ+-left-zero x
        ; isSet-Domain = isSet-ℝ
        }
      ; ∙-commute = \ {x} {y} -> ℝ+-commute x y
      }
    }

  AdditiveGroup-ℝ : AdditiveGroup AdditiveCommMonoid-ℝ
  AdditiveGroup-ℝ = record
    { -_ = ℝ-_
    ; +-inverse = \ {x} -> ℝ+-inverse x
    }
