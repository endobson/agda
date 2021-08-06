{-# OPTIONS --cubical --safe --exact-split #-}

module real.heyting-field where

open import base
open import cubical
open import equality
open import functions
open import heyting-field
open import rational
open import rational.order
open import real
open import real.sequence
open import real.arithmetic.order
open import real.arithmetic.absolute-value
open import real.arithmetic.multiplication.inverse
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import sum
open import sign
open import truncation
open import univalence
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-ring
open import ordered-ring.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real


private
  open ℝRing using (is-unit)

  diff# : ℝ -> ℝ -> Type _
  diff# x y = ℝRing.isUnit (y + (- x))

  diff#->ℝ# : {x y : ℝ} -> diff# x y -> x ℝ# y
  diff#->ℝ# {x} {y} (is-unit i path) =
    unsquash (isProp-ℝ# x y) (∥-map2 handle (split-small-absℝ d ε) (split-small-absℝ i ε))
    where
    ε : ℚ⁺
    ε = 1/2r , Pos-1/ℕ (2 , tt)
    ε' = fst ε
    εℝ = ℚ->ℝ ε'
    0<εℝ : 0ℝ < εℝ
    0<εℝ = ℚ->ℝ-preserves-< 0r ε' (Pos-0< ε' (snd ε))
    εℝ<1 : εℝ < 1ℝ
    εℝ<1 = ℚ->ℝ-preserves-< 1/2r 1r 1/2r<1r

    d = y + (- x)

    Inv-i->path : (inv : ℝInv i) -> ℝ1/ i inv == d
    Inv-i->path inv =
      sym *-left-one >=>
      *-left (sym path) >=>
      *-assoc >=>
      *-right (*-commute >=> ℝ1/-inverse i inv) >=>
      *-right-one

    Inv-i->Inv-d : ℝInv i -> ℝInv d
    Inv-i->Inv-d inv = subst ℝInv (Inv-i->path inv) (ℝ1/-preserves-ℝInv i inv)

    module _ where
      private
        p1 : (x + d) == y
        p1 = +-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero

        p2 : (x + 0ℝ) == x
        p2 = +-right-zero
      Inv-d->x#y : ℝInv d -> x ℝ# y
      Inv-d->x#y (inj-l d<0) = inj-r (subst2 _ℝ<_ p1 p2 (+₁-preserves-< x d 0ℝ d<0))
      Inv-d->x#y (inj-r 0<d) = inj-l (subst2 _ℝ<_ p2 p1 (+₁-preserves-< x 0ℝ d 0<d))

    handle : ((absℝ d ℝ< (ℚ->ℝ ε')) ⊎ ℝInv d) ->
             ((absℝ i ℝ< (ℚ->ℝ ε')) ⊎ ℝInv i) ->
             x ℝ# y
    handle (inj-r inv-d) _ = (Inv-d->x#y inv-d)
    handle (inj-l _) (inj-r inv-i) = (Inv-d->x#y (Inv-i->Inv-d inv-i))
    handle (inj-l ad<ε) (inj-l ai<ε) = bot-elim (εε≮1 εε<1)
      where
      εai≮adai : (εℝ * (absℝ i)) ≮ ((absℝ d) * (absℝ i))
      εai≮adai = *₂-preserves-≮ εℝ (absℝ d) (absℝ i) (asym-ℝ< {absℝ d} {εℝ} ad<ε) (absℝ-≮0 i)

      εε≮εai : (εℝ * εℝ) ≮ (εℝ * (absℝ i))
      εε≮εai = *₁-preserves-≮ εℝ εℝ (absℝ i) (asym-ℝ< {0ℝ} {εℝ} 0<εℝ) (asym-ℝ< {absℝ i} {εℝ} ai<ε)

      εε≮adai : (εℝ * εℝ) ≮ ((absℝ d) * (absℝ i))
      εε≮adai = trans-≮ {_} {_} {_} {εℝ * εℝ} {εℝ * (absℝ i)} {(absℝ d) * (absℝ i)} εε≮εai εai≮adai

      0<1 : 0ℝ < 1ℝ
      0<1 = (ℚ->ℝ-preserves-< 0r 1r 0<1r)

      adai=1 : ((absℝ d) * (absℝ i)) == 1ℝ
      adai=1 = sym (absℝ-distrib-* d i) >=>
               cong absℝ path >=>
               absℝ-NonNeg-idem 1ℝ (asym-ℝ< {0ℝ} {1ℝ} 0<1)

      εε≮1 : (εℝ * εℝ) ≮ 1ℝ
      εε≮1 = subst ((εℝ * εℝ) ≮_) adai=1 εε≮adai

      εε<11 : (εℝ * εℝ) < (1ℝ * 1ℝ)
      εε<11 = trans-< {_} {_} {_} {εℝ * εℝ} {εℝ * 1ℝ} {1ℝ * 1ℝ}
                      (*₁-preserves-< εℝ εℝ 1ℝ 0<εℝ εℝ<1)
                      (*₂-preserves-< εℝ 1ℝ 1ℝ εℝ<1 0<1)

      εε<1 : (εℝ * εℝ) < 1ℝ
      εε<1 = subst ((εℝ * εℝ) <_) *-right-one εε<11




  ℝ#->diff# : {x y : ℝ} -> x ℝ# y -> diff# x y
  ℝ#->diff# {x} {y} x#y = is-unit (ℝ1/ d inv) (*-commute >=> ℝ1/-inverse d inv)
    where
    d = (y + (- x))
    inv : ℝInv d
    inv = ℝ#->ℝInv x y x#y

  sym-diff# : Symmetric diff#
  sym-diff# {x} {y} (is-unit i path) =
    is-unit (- i)
      (minus-extract-right >=>
       sym minus-extract-left >=>
       *-left (minus-distrib-plus >=>
               +-commute >=>
               +-left minus-double-inverse) >=>
       path)

  irrefl-diff# : Irreflexive diff#
  irrefl-diff# {x} (is-unit i path) =
    irrefl-ℝ< {1ℝ} (subst (_ℝ< 1ℝ) 0=1 (ℚ->ℝ-preserves-< 0r 1r 0<1r))
    where
    x+-x=0 : x + (- x) == 0ℝ
    x+-x=0 = +-inverse

    0=1 : 0ℝ == 1ℝ
    0=1 =
      sym *-left-zero >=>
      *-left (sym (+-inverse)) >=>
      path

  comparison-diff# : Comparison diff#
  comparison-diff# x y z d# =
    ∥-map (⊎-map ℝ#->diff# ℝ#->diff#) (comparison-ℝ# x y z (diff#->ℝ# d#))

  tight-diff# : Tight diff#
  tight-diff# ¬d# = tight-ℝ# (¬d# ∘ ℝ#->diff#)



  TightApartness-ℝUnit : TightApartness diff#
  TightApartness-ℝUnit = tight-diff# , irrefl-diff# , sym-diff# , comparison-diff#


instance
  ℝField : Field ℝRing
  ℝField = record
    { TightApartness-f# = TightApartness-ℝUnit
    }
