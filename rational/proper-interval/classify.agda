{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.classify where

open import additive-group
open import base
open import order
open import order.instances.rational
open import rational.proper-interval.base
open import ring.implementations.rational

data Class (i : Iℚ) : Type₀ where
  nn-c : NonNegI i    -> Class i
  np-c : NonPosI i    -> Class i
  cz-c : CrossZeroI i -> Class i


data StrictClass (i : Iℚ) : Type₀ where
  p-c  : PosI i       -> StrictClass i
  n-c  : NegI i       -> StrictClass i
  cz-c : CrossZeroI i -> StrictClass i

data StrictClass' (i : Iℚ) : Type₀ where
  nn-c : NonNegI i         -> StrictClass' i
  np-c : NonPosI i         -> StrictClass' i
  cz-c : StrictCrossZeroI i -> StrictClass' i

classify : (i : Iℚ) -> Class i
classify i@(Iℚ-cons l u _) =
  handle (split-< l 0#) (split-< u 0#)
  where
  handle : (l < 0# ⊎ 0# ≤ l) -> (u < 0# ⊎ 0# ≤ u) -> Class i
  handle (inj-r 0≤l) _           = nn-c 0≤l
  handle (inj-l l<0) (inj-r 0≤u) = cz-c (weaken-< l<0 , 0≤u)
  handle (inj-l l<0) (inj-l u<0) = np-c (weaken-< u<0)


strict-classify : (i : Iℚ) -> StrictClass i
strict-classify i@(Iℚ-cons l u _) =
  handle (split-< 0# l) (split-< u 0#)
  where
  handle : (0# < l ⊎ l ≤ 0#) -> (u < 0# ⊎ 0# ≤ u) -> StrictClass i
  handle (inj-l 0<l) _           = p-c 0<l
  handle (inj-r l≤0) (inj-l u<0) = n-c u<0
  handle (inj-r l≤0) (inj-r 0≤u) = cz-c (l≤0 , 0≤u)

strict-classify' : (i : Iℚ) -> StrictClass' i
strict-classify' i@(Iℚ-cons l u _) =
  handle (split-< l 0#) (split-< 0# u)
  where
  handle : (l < 0# ⊎ 0# ≤ l) -> (0# < u ⊎ u ≤ 0#) -> StrictClass' i
  handle (inj-r 0≤l) _           = nn-c 0≤l
  handle (inj-l l<0) (inj-r u≤0) = np-c u≤0
  handle (inj-l l<0) (inj-l 0<u) = cz-c (l<0 , 0<u)
