{-# OPTIONS --cubical --safe --exact-split #-}

module isomorphism.set where

open import base
open import isomorphism
open import hlevel.base
open import hlevel.retract
open import hlevel.equivalence

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         (hA : isSet A) (hB : isSet B)
  where
  opaque
    isSet-Iso : isSet (Iso A B)
    isSet-Iso = isSet-Retract isoToEquiv equivToIso (\_ -> isSet-iso-path hA hB refl) (isSet-≃ hA hB)
