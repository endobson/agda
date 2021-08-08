{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.maxabs-multiplication where

open import base
open import equality
open import order
open import order.instances.rational
open import ordered-ring
open import rational
open import rational.minmax
open import rational.order-switch
open import rational.proper-interval
open import rational.sign
open import sign
open import sign.instances.rational

private
  i-maxabs-i-scale : (k : ℚ) (a : Iℚ) -> i-maxabs (i-scale k a) == (absℚ k) r* (i-maxabs a)
  i-maxabs-i-scale k a@(Iℚ-cons al au al≤au) = handle (decide-sign k)
    where
    nn-case : NonNeg k -> i-maxabs (i-scale k a) == (absℚ k) r* (i-maxabs a)
    nn-case nn-k =
      cong i-maxabs (sym (i-scale-NN-path (k , nn-k) a)) >=>
      cong2 maxℚ (absℚ-r* k al) (absℚ-r* k au) >=>
      maxℚ-r*₁-NonNeg (absℚ k) (absℚ al) (absℚ au) (NonNeg-absℚ k)

    np-case : NonPos k -> i-maxabs (i-scale k a) == (absℚ k) r* (i-maxabs a)
    np-case np-k =
      cong i-maxabs (sym (i-scale-NP-path (k , np-k) a)) >=>
      maxℚ-commute >=>
      cong2 maxℚ (absℚ-r* k al) (absℚ-r* k au) >=>
      maxℚ-r*₁-NonNeg (absℚ k) (absℚ al) (absℚ au) (NonNeg-absℚ k)

    handle : Σ[ s ∈ Sign ] isSign s k -> i-maxabs (i-scale k a) == (absℚ k) r* (i-maxabs a)
    handle (pos-sign  , p-k) = nn-case (inj-l p-k)
    handle (zero-sign , z-k) = nn-case (inj-r z-k)
    handle (neg-sign  , n-k) = np-case (inj-l n-k)

  maxℚ-swap : (a b c d : ℚ) -> maxℚ (maxℚ a b) (maxℚ c d) == maxℚ (maxℚ a c) (maxℚ b d)
  maxℚ-swap a b c d =
    maxℚ-assoc a b (maxℚ c d) >=>
    cong (maxℚ a) (sym (maxℚ-assoc b c d) >=> (cong (\x -> maxℚ x d) maxℚ-commute) >=>
                   (maxℚ-assoc c b d)) >=>
    sym (maxℚ-assoc a c (maxℚ b d))

  i-maxabs-i∪ : (a b : Iℚ) -> i-maxabs (a i∪ b) == maxℚ (i-maxabs a) (i-maxabs b)
  i-maxabs-i∪ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) = p1 >=> sym p2
    where
    albl≤aubu : (minℚ al bl) ℚ≤ (maxℚ au bu)
    albl≤aubu =
      trans-ℚ≤ {minℚ al bl} {al} {maxℚ au bu} (minℚ-≤-left al bl)
               (trans-ℚ≤ {al} {au} {maxℚ au bu} al≤au (maxℚ-≤-left au bu))

    p1 : i-maxabs (a i∪ b) == maxℚ (maxℚ au bu) (maxℚ (r- al) (r- bl))
    p1 = maxℚ-swap _ _ _ _ >=>
         cong2 maxℚ (maxℚ-right (minℚ al bl) (maxℚ au bu) albl≤aubu)
                    (maxℚ-left (r- (minℚ al bl)) (r- (maxℚ au bu))
                               (minus-flips-≤ (minℚ al bl) (maxℚ au bu) albl≤aubu)) >=>
         cong (maxℚ (maxℚ au bu)) (r--minℚ al bl)


    p2 : maxℚ (i-maxabs a) (i-maxabs b) ==
         maxℚ (maxℚ au bu) (maxℚ (r- al) (r- bl))
    p2 = cong2 maxℚ (maxℚ-swap _ _ _ _ >=>
                     (cong2 maxℚ (maxℚ-right al au al≤au)
                                 (maxℚ-left (r- al) (r- au) (minus-flips-≤ al au al≤au))))
                    (maxℚ-swap _ _ _ _ >=>
                     (cong2 maxℚ (maxℚ-right bl bu bl≤bu)
                                 (maxℚ-left (r- bl) (r- bu) (minus-flips-≤ bl bu bl≤bu)))) >=>
         maxℚ-swap _ _ _ _

abstract
  i-maxabs-i* : (a b : Iℚ) -> i-maxabs (a i* b) == (i-maxabs a) r* (i-maxabs b)
  i-maxabs-i* a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
    i-maxabs-i∪ (i-scale al b) (i-scale au b) >=>
    cong2 maxℚ (i-maxabs-i-scale al b) (i-maxabs-i-scale au b) >=>
    maxℚ-r*₂-NonNeg (absℚ al) (absℚ au) (i-maxabs b) (NonNeg-i-maxabs b)
