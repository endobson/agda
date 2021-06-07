{-# OPTIONS --cubical --safe --exact-split #-}

module sign.instances.fraction where

open import base
open import sign
open import rational
open import fraction.sign as fs

instance
  SignStr-ℚ' : SignStr Rational' ℓ-zero
  SignStr-ℚ' = record
    { isSign = fs.isSignℚ'
    ; isProp-isSign = fs.isProp-isSignℚ'
    ; isSign-unique = fs.isSignℚ'-unique
    }
