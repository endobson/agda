{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-distributive where

open import base
open import equality
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-semiring
open import rational
open import rational.order
open import rational.proper-interval
open import ring.implementations.rational
open import semiring
open import sign.instances.rational

private
  minℚ-r+-swap : (a b c d : ℚ) -> (min a b r+ min c d) ℚ≤ min (a r+ c) (b r+ d)
  minℚ-r+-swap a b c d =
    min-property {P = (min a b r+ min c d) ℚ≤_} (a r+ c) (b r+ d) abcd≤ac abcd≤bd
    where
    abcd≤ac = +-preserves-≤ min-≤-left min-≤-left
    abcd≤bd = +-preserves-≤ min-≤-right min-≤-right

  maxℚ-r+-swap : (a b c d : ℚ) -> max (a r+ c) (b r+ d) ℚ≤ (max a b r+ max c d)
  maxℚ-r+-swap a b c d =
    max-property {P = _ℚ≤ (max a b r+ max c d)} (a r+ c) (b r+ d) ac≤abcd bd≤abcd
    where
    ac≤abcd = +-preserves-≤ max-≤-left max-≤-left
    bd≤abcd = +-preserves-≤ max-≤-right max-≤-right

i-scale-distrib-r+ : (k1 k2 : ℚ) (a : Iℚ) -> i-scale (k1 r+ k2) a i⊆ (i-scale k1 a i+ i-scale k2 a)
i-scale-distrib-r+ k1 k2 a@(Iℚ-cons al au al≤au) = (i⊆-cons lt1 lt2)
  where
  case1 : Iℚ.l (i-scale (k1 r+ k2) a) == min ((k1 r* al) r+ (k2 r* al)) ((k1 r* au) r+ (k2 r* au))
  case1 = cong2 min *-distrib-+-right *-distrib-+-right

  case2 : Iℚ.l ((i-scale k1 a) i+ (i-scale k2 a)) ==
          (min (k1 r* al) (k1 r* au)) r+ (min (k2 r* al) (k2 r* au))
  case2 = refl

  lt1 : Iℚ.l ((i-scale k1 a) i+ (i-scale k2 a)) ℚ≤ Iℚ.l (i-scale (k1 r+ k2) a)
  lt1 = subst2 _ℚ≤_ (sym case2) (sym case1) (minℚ-r+-swap _ _ _ _)

  case3 : Iℚ.u (i-scale (k1 r+ k2) a) == max ((k1 r* al) r+ (k2 r* al)) ((k1 r* au) r+ (k2 r* au))
  case3 = cong2 max *-distrib-+-right *-distrib-+-right

  case4 : Iℚ.u ((i-scale k1 a) i+ (i-scale k2 a)) ==
          (max (k1 r* al) (k1 r* au)) r+ (max (k2 r* al) (k2 r* au))
  case4 = refl

  lt2 : Iℚ.u (i-scale (k1 r+ k2) a) ℚ≤ Iℚ.u ((i-scale k1 a) i+ (i-scale k2 a))
  lt2 = subst2 _ℚ≤_ (sym case3) (sym case4) (maxℚ-r+-swap _ _ _ _)

i*-distrib-i+-left : (a b c : Iℚ) -> (a i* (b i+ c)) i⊆ ((a i* b) i+ (a i* c))
i*-distrib-i+-left a@(Iℚ-cons al au _) b c =
  subst ((a i* (b i+ c)) i⊆_) (i∪-same abac) (i∪-preserves-⊆ l-⊆ u-⊆)
  where
  abac = ((a i* b) i+ (a i* c))
  l-⊆ : i-scale al (b i+ c) i⊆ abac
  l-⊆ = subst (_i⊆ abac) (sym (i-scale-distrib-i+ al b c))
              (i+-preserves-⊆ (i∪₁-⊆ (i-scale al b) (i-scale au b))
                              (i∪₁-⊆ (i-scale al c) (i-scale au c)))

  u-⊆ : i-scale au (b i+ c) i⊆ abac
  u-⊆ = subst (_i⊆ abac) (sym (i-scale-distrib-i+ au b c))
              (i+-preserves-⊆ (i∪₂-⊆ (i-scale al b) (i-scale au b))
                              (i∪₂-⊆ (i-scale al c) (i-scale au c)))


i*-distrib-i+-right : (a b c : Iℚ) -> ((a i+ b) i* c) i⊆ ((a i* c) i+ (b i* c))
i*-distrib-i+-right a b c =
  subst2 _i⊆_ (i*-commute c (a i+ b)) (cong2 _i+_ (i*-commute c a) (i*-commute c b))
         (i*-distrib-i+-left c a b)
