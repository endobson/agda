{-# OPTIONS --cubical --safe --exact-split #-}

module sign.instances.rational where

open import base
open import sign
open import rational
open import rational.sign as rs

instance
  SignStr-ℚ : SignStr ℚ ℓ-zero
  SignStr-ℚ = record
    { isSign = rs.isSignℚ
    ; isProp-isSign = rs.isProp-isSignℚ
    ; isSign-unique = rs.isSignℚ-unique
    }
