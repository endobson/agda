{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.multiplication-inclusion where

open import base
open import equality
open import rational.open-interval

import rational.proper-interval as closed
import rational.proper-interval.multiplication-inclusion as closed

i*-preserves-⊂ : {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) -> (a i* c) i⊂ (b i* d)
i*-preserves-⊂ {a} {b} {c} {d} a⊂b c⊂d =
  OI->CI-reflects-⊂
    (subst2 closed._i⊂_
      (closed.Iℚ-bounds-path refl refl)
      (closed.Iℚ-bounds-path refl refl)
      (closed.i*-preserves-⊂
        (OI->CI-preserves-⊂ a⊂b)
        (OI->CI-preserves-⊂ c⊂d)))
