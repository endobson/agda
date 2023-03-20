{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.nat where

open import additive-group
open import base
open import nat

instance
  AdditiveCommMonoid-Nat : AdditiveCommMonoid Nat
  AdditiveCommMonoid-Nat = record
    { comm-monoid = record
      { monoid = record
        { ε = 0
        ; _∙_ = _+'_
        ; ∙-assoc = \ {m} {n} {o} -> +'-assoc {m} {n} {o}
        ; ∙-left-ε = refl
        ; ∙-right-ε = +'-right-zero
        ; isSet-Domain = isSetNat
        }
      ; ∙-commute = \ {m} {n} -> +'-commute {m} {n}
      }
    }
