{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.multiplication-distributive where

open import rational.open-interval
open import equality
open import base

import rational.proper-interval as closed
import rational.proper-interval.multiplication-distributive as closed-distrib

opaque
  i*-distrib-i+-left : (a b c : Iℚ) -> (a i* (b i+ c)) i⊆ ((a i* b) i+ (a i* c))
  i*-distrib-i+-left a b c =
    OI->CI-reflects-⊆
      (subst2 closed._i⊆_
        (closed.Iℚ-bounds-path refl refl) (closed.Iℚ-bounds-path refl refl)
        (closed-distrib.i*-distrib-i+-left (OI->CI a) (OI->CI b) (OI->CI c)))

  i*-distrib-i+-right : (a b c : Iℚ) -> ((a i+ b) i* c) i⊆ ((a i* c) i+ (b i* c))
  i*-distrib-i+-right a b c =
    OI->CI-reflects-⊆
      (subst2 closed._i⊆_
        (closed.Iℚ-bounds-path refl refl) (closed.Iℚ-bounds-path refl refl)
        (closed-distrib.i*-distrib-i+-right (OI->CI a) (OI->CI b) (OI->CI c)))
