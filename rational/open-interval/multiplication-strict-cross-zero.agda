{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.multiplication-strict-cross-zero where

open import base
open import equality
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-ring
open import ordered-semiring
open import rational
open import rational.order
open import rational.open-interval
open import relation
open import sign
open import additive-group
open import sign.instances.rational


private
  StrictCrossZeroI : Pred Iℚ ℓ-zero
  StrictCrossZeroI a = (Iℚ.l a) < 0# × 0# < (Iℚ.u a)

i*₁-StrictCrossZero : (a b : Iℚ) -> StrictCrossZeroI a -> StrictCrossZeroI (a i* b)
i*₁-StrictCrossZero a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl<bu) (n-al , p-au) =
  handle (split-< bl 0r)
  where
  bl≤bu = weaken-< bl<bu
  l = min (min (al r* bl) (al r* bu)) (min (au r* bl) (au r* bu))

  l-p : l == min (al r* bu) (au r* bl)
  l-p = cong2 min (min-≥-path (*₁-flips-≤ (weaken-< n-al) bl≤bu))
                  (min-≤-path (*₁-preserves-≤ (weaken-< p-au) bl≤bu))

  u = max (max (al r* bl) (al r* bu)) (max (au r* bl) (au r* bu))


  u-p : u == max (al r* bl) (au r* bu)
  u-p = cong2 max (max-≥-path (*₁-flips-≤ (weaken-< n-al) bl≤bu))
                  (max-≤-path (*₁-preserves-≤ (weaken-< p-au) bl≤bu))


  n-case : Neg bl -> StrictCrossZeroI (a i* b)
  n-case n-bl = n-l , p-u
    where
    n-l : Neg l
    n-l = Neg-≤ l (au r* bl) (r*₁-preserves-sign (au , p-au) bl {neg-sign} n-bl)
                  (subst (_ℚ≤ (au r* bl)) (sym l-p) min-≤-right)
    p-u : Pos u
    p-u = Pos-≤ (al r* bl) u (r*₁-flips-sign (al , n-al) bl {neg-sign} n-bl)
                (subst ((al r* bl) ℚ≤_) (sym u-p) max-≤-left)

  p-case : Pos bu -> StrictCrossZeroI (a i* b)
  p-case p-bu = n-l , p-u
    where
    n-l : Neg l
    n-l = Neg-≤ l (al r* bu) (r*₁-flips-sign (al , n-al) bu {pos-sign} p-bu)
                  (subst (_ℚ≤ (al r* bu)) (sym l-p) min-≤-left)
    p-u : Pos u
    p-u = Pos-≤ (au r* bu) u (r*₁-preserves-sign (au , p-au) bu {pos-sign} p-bu)
                (subst ((au r* bu) ℚ≤_) (sym u-p) max-≤-right)


  handle : (bl < 0r ⊎ 0r ℚ≤ bl) -> StrictCrossZeroI (a i* b)
  handle (inj-l bl<0) = n-case (<0-Neg bl bl<0)
  handle (inj-r 0≤bl) = p-case (Pos-< bl bu (0≤-NonNeg bl 0≤bl) bl<bu)
