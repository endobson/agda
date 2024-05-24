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
  i-maxabs-i-scale k a@(Iℚ-cons al au al≤au) = handle (split-< 0# k)
    where
    nn-case : 0# ≤ k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    nn-case 0≤k =
      cong i-maxabs (sym (i-scale-0≤-path (k , 0≤k) a)) >=>
      cong2 max (sym minus-extract-right) refl >=>
      sym (*-distrib-max-left 0≤k) >=>
      *-left (sym (abs-0≤-path 0≤k))

    np-case : k ≤ 0# -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    np-case k≤0 =
      cong i-maxabs (sym (i-scale-≤0-path (k , k≤0) a)) >=>
      cong2 max (sym minus-extract-left) (sym minus-extract-both) >=>
      max-commute >=>
      sym (*-distrib-max-left (minus-flips-≤0 k≤0)) >=>
      *-left (sym (abs-≤0-path k≤0))


    handle : (0# < k ⊎ k ≤ 0#) -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    handle (inj-l 0<k) = nn-case (weaken-< 0<k)
    handle (inj-r k≤0) = np-case k≤0

  i-maxabs-i∪ : (a b : Iℚ) -> i-maxabs (a i∪ b) == max (i-maxabs a) (i-maxabs b)
  i-maxabs-i∪ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    cong2 max minus-min-path refl >=> max-swap


abstract
  i-maxabs-i* : (a b : Iℚ) -> i-maxabs (a i* b) == (i-maxabs a) r* (i-maxabs b)
  i-maxabs-i* a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    i-maxabs-i∪ (i-scale al b) (i-scale au b) >=>
    cong2 max (i-maxabs-i-scale al b) (i-maxabs-i-scale au b) >=>
    sym (*-distrib-max-right (0≤i-maxabs b)) >=>
    *-left (i-maxabs'-path a)
