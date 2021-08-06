{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-inverse where

open import base
open import equality
open import order
open import order.instances.rational
open import rational
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import sign
open import sign.instances.rational

i1/-Pos : (a : Iℚ) -> PosI a -> Iℚ
i1/-Pos (Iℚ-cons al au al≤au) pos-al = Iℚ-cons au' al' au'≤al'
  where
  pos-au = Pos-≤ al au pos-al al≤au
  inv-al = Pos->Inv pos-al
  inv-au = Pos->Inv pos-au
  al' = r1/ al inv-al
  au' = r1/ au inv-au
  au'≤al' = r1/-Pos-flips-≤ (al , pos-al) (au , pos-au) al≤au
