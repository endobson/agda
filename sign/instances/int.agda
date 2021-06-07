{-# OPTIONS --cubical --safe --exact-split #-}

module sign.instances.int where

open import base
import int.sign as i
open import int.base
open import sign

instance
  SignStr-ℤ : SignStr ℤ ℓ-zero
  SignStr-ℤ = record
    { isSign = i.isSign
    ; isProp-isSign = \s _ -> i.isProp-isSign s
    ; isSign-unique = \_ _ _ -> i.isSign-unique
    }
