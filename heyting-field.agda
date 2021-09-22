{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field where

open import additive-group
open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import funext
open import relation
open import ring
open import semiring
open import sigma
open import truncation

private
  variable
    ℓ : Level

record Field {ℓ : Level} {D : Type ℓ}
             {ACM : AdditiveCommMonoid D}
             {S : Semiring ACM} (R : Ring S) (A : TightApartnessStr D)
  : Type (ℓ-suc ℓ) where
  private
    module R = Ring R
    instance
      IACM = ACM
      IS = S
      IR = R
      IA = A

  _f#_ : D -> D -> Type ℓ
  x f# y = R.isUnit (y + (- x))

  field
    f#-path : _f#_ == (TightApartnessStr._#_ A)


  TightApartness-f# : TightApartness _f#_
  TightApartness-f# = subst TightApartness (sym f#-path) (TightApartnessStr.TightApartness-# A)

  sym-f# : Symmetric _f#_
  sym-f# = fst (snd (snd TightApartness-f#))

  comparison-f# : Comparison _f#_
  comparison-f# = snd (snd (snd TightApartness-f#))

  private
    1#0' : 1# f# 0#
    1#0' = sym-f# (subst R.isUnit (sym +-right-zero >=> +-right (sym minus-zero)) R.isUnit-one)

  1#0 : 1# # 0#
  1#0 = subst (\z -> z 1# 0#) f#-path 1#0'

  TightApartnessStr-f# : TightApartnessStr D
  TightApartnessStr-f# = record
    { _#_ = _f#_
    ; TightApartness-# = TightApartness-f#
    ; isProp-# = (\_ _ -> R.isProp-isUnit)
    }

  f#-equiv : {x y : D} -> (x f# y) ≃ (x # y)
  f#-equiv {x} {y} = subst (\op -> (x f# y) ≃ op x y) f#-path (idEquiv (x f# y))

  f#0->isUnit : {x : D} -> x f# 0# -> R.isUnit x
  f#0->isUnit x#0 =
    subst R.isUnit minus-double-inverse (R.u--closed (subst R.isUnit +-left-zero x#0))

  #0->isUnit : {x : D} -> x # 0# -> R.isUnit x
  #0->isUnit {x} x#0 = f#0->isUnit (subst (\f -> f x 0#) (sym f#-path) x#0)

  isUnit->f#0 : {x : D} -> R.isUnit x -> x f# 0#
  isUnit->f#0 ux = subst R.isUnit (sym +-left-zero) (R.u--closed ux)

  isUnit->#0 : {x : D} -> R.isUnit x -> x # 0#
  isUnit->#0 ux = eqFun f#-equiv (isUnit->f#0 ux)


  *-apart-zero : {x y : D} -> (x * y) # 0# -> (x # 0#) × (y # 0#)
  *-apart-zero xy#0 = ×-map isUnit->#0 isUnit->#0 (R.*-isUnit-split (#0->isUnit xy#0))

  *₁-apart-args : {x y z : D} -> ((x * y) # (x * z)) -> (x # 0#) × (y # z)
  *₁-apart-args {x} {y} {z} xy#yz =
    isUnit->#0 (fst (R.*-isUnit-split u2)) , (eqFun f#-equiv (snd (R.*-isUnit-split u2)))
    where
    u2 : R.isUnit (x * (z + (- y)))
    u2 = subst R.isUnit (+-right (sym minus-extract-right) >=> sym *-distrib-+-left)
                        (eqInv f#-equiv xy#yz)

  *-apart-args : {x y z w : D} -> (x * y) # (z * w) -> ∥ (x # z) ⊎ (y # w) ∥
  *-apart-args {x} {y} {z} {w} xy#zw = ∥-bind handle #xw
    where
    #xw : ∥ ((x * y) # (x * w)) ⊎ ((x * w) # (z * w)) ∥
    #xw = comparison-# (x * y) (x * w) (z * w) xy#zw

    handle : ((x * y) # (x * w)) ⊎ ((x * w) # (z * w)) ->
             ∥ (x # z) ⊎ (y # w) ∥
    handle (inj-l xy#xw) = ∣ inj-r (snd (*₁-apart-args xy#xw)) ∣
    handle (inj-r xw#zw) = ∣ inj-l (snd (*₁-apart-args wx#wz)) ∣
      where
      wx#wz : (w * x) # (w * z)
      wx#wz = subst2 _#_ *-commute *-commute xw#zw

  StronglyInjective-- : StronglyInjective -_
  StronglyInjective-- {x} {y} x#y = subst (\f -> f (- x) (- y)) f#-path isUnit--d
    where
    isUnit-d = subst (\f -> f x y) (sym f#-path) x#y
    isUnit--d : R.isUnit (diff (- x) (- y))
    isUnit--d = subst R.isUnit minus-distrib-plus (R.u--closed isUnit-d)

  StronglyInjective-*₁ : {x : D} -> x # 0# -> StronglyInjective (x *_)
  StronglyInjective-*₁ {x} x#0 {a} {b} a#b = xa#xb
    where
    isUnit-x = #0->isUnit x#0
    af#b = eqInv f#-equiv a#b
    isUnit-xd = R.u*-closed isUnit-x af#b
    isUnit-xaxb = subst R.isUnit *-distrib-diff-left isUnit-xd
    xa#xb = eqFun f#-equiv isUnit-xaxb

  StronglyInjective-+₁ : {x : D} -> StronglyInjective (x +_)
  StronglyInjective-+₁ {x} {a} {b} a#b = xa#xb
    where
    d=d2 : diff a b == diff (x + a) (x + b)
    d=d2 = sym +-left-zero >=> +-left (sym +-inverse) >=> +-swap-diff
    af#b = eqInv f#-equiv a#b
    xaf#xb = subst R.isUnit d=d2 af#b
    xa#xb = eqFun f#-equiv xaf#xb

  StronglyInjective-+₂ : {x : D} -> StronglyInjective (_+ x)
  StronglyInjective-+₂ {x} = subst StronglyInjective (funExt (\_ -> +-commute)) StronglyInjective-+₁
