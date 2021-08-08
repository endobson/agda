{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-strict-cross-zero where

open import base
open import equality
open import order
open import order.instances.rational
open import rational
open import rational.minmax
open import rational.order-switch
open import rational.proper-interval
open import sign
open import sign.instances.rational


i*₁-StrictCrossZero : (a b : Iℚ) -> StrictCrossZeroI a -> NonConstantI b -> StrictCrossZeroI (a i* b)
i*₁-StrictCrossZero a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) (n-al , p-au) bl<bu =
  handle (split-< bl 0r)
  where
  l = minℚ (minℚ (al r* bl) (al r* bu)) (minℚ (au r* bl) (au r* bu))

  l-p : l == minℚ (al r* bu) (au r* bl)
  l-p = cong2 minℚ (minℚ-right (al r* bl) (al r* bu)
                               (r*₁-flips-≤ (al , (inj-l n-al)) bl bu bl≤bu))
                   (minℚ-left (au r* bl) (au r* bu)
                              (r*₁-preserves-≤ (au , (inj-l p-au)) bl bu bl≤bu))

  u = maxℚ (maxℚ (al r* bl) (al r* bu)) (maxℚ (au r* bl) (au r* bu))


  u-p : u == maxℚ (al r* bl) (au r* bu)
  u-p = cong2 maxℚ (maxℚ-left (al r* bl) (al r* bu)
                              (r*₁-flips-≤ (al , (inj-l n-al)) bl bu bl≤bu))
                   (maxℚ-right (au r* bl) (au r* bu)
                               (r*₁-preserves-≤ (au , (inj-l p-au)) bl bu bl≤bu))


  n-case : Neg bl -> StrictCrossZeroI (a i* b)
  n-case n-bl = n-l , p-u
    where
    n-l : Neg l
    n-l = Neg-≤ l (au r* bl) (r*₁-preserves-sign (au , p-au) bl {neg-sign} n-bl)
                  (subst (_ℚ≤ (au r* bl)) (sym l-p) (minℚ-≤-right (al r* bu) (au r* bl)))
    p-u : Pos u
    p-u = Pos-≤ (al r* bl) u (r*₁-flips-sign (al , n-al) bl {neg-sign} n-bl)
                (subst ((al r* bl) ℚ≤_) (sym u-p) (maxℚ-≤-left (al r* bl) (au r* bu)))

  p-case : Pos bu -> StrictCrossZeroI (a i* b)
  p-case p-bu = n-l , p-u
    where
    n-l : Neg l
    n-l = Neg-≤ l (al r* bu) (r*₁-flips-sign (al , n-al) bu {pos-sign} p-bu)
                  (subst (_ℚ≤ (al r* bu)) (sym l-p) (minℚ-≤-left (al r* bu) (au r* bl)))
    p-u : Pos u
    p-u = Pos-≤ (au r* bu) u (r*₁-preserves-sign (au , p-au) bu {pos-sign} p-bu)
                (subst ((au r* bu) ℚ≤_) (sym u-p) (maxℚ-≤-right (al r* bl) (au r* bu)))


  handle : (bl < 0r ⊎ 0r ℚ≤ bl) -> StrictCrossZeroI (a i* b)
  handle (inj-l bl<0) = n-case (<0-Neg bl bl<0)
  handle (inj-r 0≤bl) = p-case (Pos-< bl bu (0≤-NonNeg bl 0≤bl) bl<bu)
