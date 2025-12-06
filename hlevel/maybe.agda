{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.maybe where

open import base
open import hlevel.base
open import hlevel.sum
open import hlevel.isomorphism
open import isomorphism
open import maybe

opaque
  isSet-Maybe : {ℓA : Level} {A : Type ℓA} -> isSet A -> isSet (Maybe A)
  isSet-Maybe {ℓA} {A} hA = iso-isSet i (isSet-⊎ isSetTop hA)
    where
    i : Iso (Top ⊎ A) (Maybe A)
    i .Iso.fun (inj-l tt) = nothing
    i .Iso.fun (inj-r a) = just a
    i .Iso.inv nothing = (inj-l tt)
    i .Iso.inv (just a) = (inj-r a)
    i .Iso.leftInv (inj-l tt) = refl
    i .Iso.leftInv (inj-r a) = refl
    i .Iso.rightInv nothing = refl
    i .Iso.rightInv (just a) = refl
