{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field where

open import apartness
open import base
open import equality
open import relation
open import ring
open import semiring
open import sigma
open import truncation

private
  variable
    ℓ : Level

record Field {ℓ : Level} {D : Type ℓ} {S : Semiring D} (R : Ring S) : Type ℓ where
  private
    module R = Ring R
    instance
      IS = S
      IR = R

  _f#_ : D -> D -> Type ℓ
  x f# y = R.isUnit (y + (- x))

  field
    TightApartness-f# : TightApartness _f#_

  sym-f# : Symmetric _f#_
  sym-f# = fst (snd (snd TightApartness-f#))

  comparison-f# : Comparison _f#_
  comparison-f# = snd (snd (snd TightApartness-f#))

  1#0 : 1# f# 0#
  1#0 = sym-f# (subst R.isUnit (sym +-right-zero >=> +-right (sym minus-zero)) R.isUnit-one)

  TightApartnessStr-f# : TightApartnessStr D
  TightApartnessStr-f# = record
    { _#_ = _f#_
    ; TightApartness-# = TightApartness-f#
    ; isProp-# = (\_ _ -> R.isProp-isUnit)
    }

  #0->isUnit : {x : D} -> x f# 0# -> R.isUnit x
  #0->isUnit x#0 =
    subst R.isUnit minus-double-inverse (R.u--closed (subst R.isUnit +-left-zero x#0))

  isUnit->#0 : {x : D} -> R.isUnit x -> x f# 0#
  isUnit->#0 ux = subst R.isUnit (sym +-left-zero) (R.u--closed ux)

  *-apart-zero : {x y : D} -> (x * y) f# 0# -> (x f# 0#) × (y f# 0#)
  *-apart-zero xy#0 = ×-map isUnit->#0 isUnit->#0 (R.*-isUnit-split (#0->isUnit xy#0))

  *₁-apart-args : {x y z : D} -> ((x * y) f# (x * z)) -> (x f# 0#) × (y f# z)
  *₁-apart-args {x} {y} {z} xy#yz =
    isUnit->#0 (fst (R.*-isUnit-split u2)) , (snd (R.*-isUnit-split u2))
    where
    u1 : R.isUnit ((x * z) + (- (x * y)))
    u1 = xy#yz

    u2 : R.isUnit (x * (z + (- y)))
    u2 = subst R.isUnit (+-right (sym minus-extract-right) >=> sym *-distrib-+-left) u1

  *-apart-args : {x y z w : D} -> (x * y) f# (z * w) -> ∥ (x f# z) ⊎ (y f# w) ∥
  *-apart-args {x} {y} {z} {w} xy#zw = ∥-bind handle #xw
    where
    #xw : ∥ ((x * y) f# (x * w)) ⊎ ((x * w) f# (z * w)) ∥
    #xw = comparison-f# (x * y) (x * w) (z * w) xy#zw

    handle : ((x * y) f# (x * w)) ⊎ ((x * w) f# (z * w)) ->
             ∥ (x f# z) ⊎ (y f# w) ∥
    handle (inj-l xy#xw) = ∣ inj-r (snd (*₁-apart-args xy#xw)) ∣
    handle (inj-r xw#zw) = ∣ inj-l (snd (*₁-apart-args wx#wz)) ∣
      where
      wx#wz : (w * x) f# (w * z)
      wx#wz = subst2 _f#_ *-commute *-commute xw#zw
