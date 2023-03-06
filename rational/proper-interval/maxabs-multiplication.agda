{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.maxabs-multiplication where

open import base
open import equality
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
open import sign
open import sign.instances.rational

private
  i-maxabs-i-scale : (k : ℚ) (a : Iℚ) -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
  i-maxabs-i-scale k a@(Iℚ-cons al au al≤au) = handle (decide-sign k)
    where
    nn-case : NonNeg k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    nn-case nn-k =
      cong i-maxabs (sym (i-scale-NN-path (k , nn-k) a)) >=>
      cong2 max abs-distrib-* abs-distrib-* >=>
      sym (*-distrib-max-left abs-0≤)

    np-case : NonPos k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    np-case np-k =
      cong i-maxabs (sym (i-scale-NP-path (k , np-k) a)) >=>
      max-commute >=>
      cong2 max abs-distrib-* abs-distrib-* >=>
      sym (*-distrib-max-left abs-0≤)

    handle : Σ[ s ∈ Sign ] isSign s k -> i-maxabs (i-scale k a) == (abs k) r* (i-maxabs a)
    handle (pos-sign  , p-k) = nn-case (inj-l p-k)
    handle (zero-sign , z-k) = nn-case (inj-r z-k)
    handle (neg-sign  , n-k) = np-case (inj-l n-k)

  maxℚ-swap : (a b c d : ℚ) -> max (max a b) (max c d) == max (max a c) (max b d)
  maxℚ-swap a b c d =
    max-assoc >=>
    cong (max a) (sym max-assoc >=> (cong (\x -> max x d) max-commute) >=>
                   max-assoc) >=>
    sym max-assoc

  i-maxabs-i∪ : (a b : Iℚ) -> i-maxabs (a i∪ b) == max (i-maxabs a) (i-maxabs b)
  i-maxabs-i∪ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) = p1 >=> sym p2
    where
    albl≤aubu : (min al bl) ℚ≤ (max au bu)
    albl≤aubu =
      trans-ℚ≤ {min al bl} {al} {max au bu} min-≤-left
               (trans-ℚ≤ {al} {au} {max au bu} al≤au max-≤-left)

    p1 : i-maxabs (a i∪ b) == max (max au bu) (max (r- al) (r- bl))
    p1 = maxℚ-swap _ _ _ _ >=>
         cong2 max (max-≤-path albl≤aubu)
                   (max-≥-path (minus-flips-≤ albl≤aubu)) >=>
         cong (max (max au bu)) minus-min-path


    p2 : max (i-maxabs a) (i-maxabs b) ==
         max (max au bu) (max (r- al) (r- bl))
    p2 = cong2 max (maxℚ-swap _ _ _ _ >=>
                    (cong2 max (max-≤-path al≤au)
                               (max-≥-path (minus-flips-≤ al≤au))))
                   (maxℚ-swap _ _ _ _ >=>
                    (cong2 max (max-≤-path bl≤bu)
                               (max-≥-path (minus-flips-≤ bl≤bu)))) >=>
         maxℚ-swap _ _ _ _

abstract
  i-maxabs-i* : (a b : Iℚ) -> i-maxabs (a i* b) == (i-maxabs a) r* (i-maxabs b)
  i-maxabs-i* a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    i-maxabs-i∪ (i-scale al b) (i-scale au b) >=>
    cong2 max (i-maxabs-i-scale al b) (i-maxabs-i-scale au b) >=>
    sym (*-distrib-max-right (NonNeg-0≤ _ (NonNeg-i-maxabs b)))
