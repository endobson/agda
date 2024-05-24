{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.multiplication-assoc where

open import base
open import equality
open import rational.open-interval

import rational.proper-interval.multiplication-assoc as closed-assoc
import rational.proper-interval as closed

module _ (a b c : Iℚ) where
  private
    closed-path = closed-assoc.i*-assoc (fst (OI->ΣCI a)) (fst (OI->ΣCI b)) (fst (OI->ΣCI c))

  opaque
    i*-assoc : a i* (b i* c) == (a i* b) i* c
    i*-assoc = Iℚ-bounds-path (cong closed.Iℚ.l closed-path) (cong closed.Iℚ.u closed-path)
