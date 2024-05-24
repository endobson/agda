{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.maxabs-multiplication where

open import base
open import rational
open import rational.open-interval

import rational.proper-interval.maxabs-multiplication as closed

opaque
  i-maxabs-i* : (a b : Iℚ) -> i-maxabs (a i* b) == (i-maxabs a) r* (i-maxabs b)
  i-maxabs-i* a@(Iℚ-cons _ _ _) b@(Iℚ-cons _ _ _) = closed.i-maxabs-i* (fst (OI->ΣCI a)) (fst (OI->ΣCI b))
