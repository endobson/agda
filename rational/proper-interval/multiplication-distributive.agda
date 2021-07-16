{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-distributive where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import rational.proper-interval
open import relation hiding (_⊆_)
open import ring.implementations.rational
open import semiring
open import sign
open import sign.instances.rational
open import truncation

private
  minℚ-r+-swap : (a b c d : ℚ) -> (minℚ a b r+ minℚ c d) ℚ≤ minℚ (a r+ c) (b r+ d)
  minℚ-r+-swap a b c d =
    minℚ-property {P = (minℚ a b r+ minℚ c d) ℚ≤_} (a r+ c) (b r+ d) abcd≤ac abcd≤bd
    where
    ab≤a = minℚ-≤-left a b
    ab≤b = minℚ-≤-right a b
    cd≤c = minℚ-≤-left c d
    cd≤d = minℚ-≤-right c d

    abcd≤ac = r+-both-preserves-≤ (minℚ a b) _ (minℚ c d) _ ab≤a cd≤c
    abcd≤bd = r+-both-preserves-≤ (minℚ a b) _ (minℚ c d) _ ab≤b cd≤d


  maxℚ-r+-swap : (a b c d : ℚ) -> maxℚ (a r+ c) (b r+ d) ℚ≤ (maxℚ a b r+ maxℚ c d)
  maxℚ-r+-swap a b c d =
    maxℚ-property {P = _ℚ≤ (maxℚ a b r+ maxℚ c d)} (a r+ c) (b r+ d) ac≤abcd bd≤abcd
    where
    a≤ab = maxℚ-≤-left a b
    b≤ab = maxℚ-≤-right a b
    c≤cd = maxℚ-≤-left c d
    d≤cd = maxℚ-≤-right c d

    ac≤abcd = r+-both-preserves-≤ _ (maxℚ a b) _ (maxℚ c d) a≤ab c≤cd
    bd≤abcd = r+-both-preserves-≤ _ (maxℚ a b) _ (maxℚ c d) b≤ab d≤cd

i-scale-distrib-r+ : (k1 k2 : ℚ) (a : Iℚ) -> i-scale (k1 r+ k2) a i⊆ (i-scale k1 a i+ i-scale k2 a)
i-scale-distrib-r+ k1 k2 a@(Iℚ-cons al au al≤au) = (i⊆-cons lt1 lt2)
  where
  case1 : Iℚ.l (i-scale (k1 r+ k2) a) == minℚ ((k1 r* al) r+ (k2 r* al)) ((k1 r* au) r+ (k2 r* au))
  case1 = cong2 minℚ *-distrib-+-right *-distrib-+-right

  case2 : Iℚ.l ((i-scale k1 a) i+ (i-scale k2 a)) ==
          (minℚ (k1 r* al) (k1 r* au)) r+ (minℚ (k2 r* al) (k2 r* au))
  case2 = refl

  lt1 : Iℚ.l ((i-scale k1 a) i+ (i-scale k2 a)) ℚ≤ Iℚ.l (i-scale (k1 r+ k2) a)
  lt1 = subst2 _ℚ≤_ (sym case2) (sym case1) (minℚ-r+-swap _ _ _ _)

  case3 : Iℚ.u (i-scale (k1 r+ k2) a) == maxℚ ((k1 r* al) r+ (k2 r* al)) ((k1 r* au) r+ (k2 r* au))
  case3 = cong2 maxℚ *-distrib-+-right *-distrib-+-right

  case4 : Iℚ.u ((i-scale k1 a) i+ (i-scale k2 a)) ==
          (maxℚ (k1 r* al) (k1 r* au)) r+ (maxℚ (k2 r* al) (k2 r* au))
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
