{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.maxabs-multiplication where

open import additive-group
open import base
open import equality
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.minmax
open import ordered-ring.absolute-value
open import ordered-semiring.minmax
open import rational
open import rational.order
open import rational.proper-interval
open import ring
open import semiring
open import sign
open import sign.instances.rational

private
  i-maxabs-i-scale : (k : ℚ) (a : Iℚ) -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
  i-maxabs-i-scale k a@(Iℚ-cons al au al≤au) = handle (decide-sign k)
    where
    nn-case : NonNeg k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    nn-case nn-k =
      cong i-maxabs (sym (i-scale-NN-path (k , nn-k) a)) >=>
      cong2 max (sym minus-extract-right) refl >=>
      sym (*-distrib-max-left 0≤k) >=>
      *-left (sym (abs-0≤-path 0≤k))
      where
      0≤k : 0# ≤ k
      0≤k = (NonNeg-0≤ _ nn-k)

    np-case : NonPos k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    np-case np-k =
      cong i-maxabs (sym (i-scale-NP-path (k , np-k) a)) >=>
      cong2 max (sym minus-extract-left) (sym minus-extract-both) >=>
      max-commute >=>
      sym (*-distrib-max-left (minus-flips-≤0 k≤0)) >=>
      *-left (sym (abs-≤0-path k≤0))
      where
      k≤0 : k ≤ 0#
      k≤0 = (NonPos-≤0 _ np-k)


    handle : Σ[ s ∈ Sign ] isSign s k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    handle (pos-sign  , p-k) = nn-case (inj-l p-k)
    handle (zero-sign , z-k) = nn-case (inj-r z-k)
    handle (neg-sign  , n-k) = np-case (inj-l n-k)

  i-maxabs-i∪ : (a b : Iℚ) -> i-maxabs (a i∪ b) == max (i-maxabs a) (i-maxabs b)
  i-maxabs-i∪ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    cong2 max minus-min-path refl >=> max-swap


abstract
  i-maxabs-i* : (a b : Iℚ) -> i-maxabs (a i* b) == (i-maxabs a) r* (i-maxabs b)
  i-maxabs-i* a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    i-maxabs-i∪ (i-scale al b) (i-scale au b) >=>
    cong2 max (i-maxabs-i-scale al b) (i-maxabs-i-scale au b) >=>
    sym (*-distrib-max-right (NonNeg-0≤ _ (NonNeg-i-maxabs b))) >=>
    *-left (i-maxabs'-path a)
