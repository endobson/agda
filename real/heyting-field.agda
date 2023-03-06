{-# OPTIONS --cubical --safe --exact-split #-}

module real.heyting-field where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import functions
open import funext
open import heyting-field
open import isomorphism
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-integral-domain
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.arithmetic.absolute-value
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.order
open import real.order
open import real.rational
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import sum
open import truncation
open import univalence


private
  open ℝRing using (is-unit)

  diff# : ℝ -> ℝ -> Type _
  diff# x y = ℝRing.isUnit (y + (- x))

  diff#->ℝ# : {x y : ℝ} -> diff# x y -> x # y
  diff#->ℝ# {x} {y} (is-unit i path) =
    unsquash isProp-# (∥-map2 handle (split-small-absℝ d ε) (split-small-absℝ i ε))
    where
    ε : ℚ⁺
    ε = 1/2r , Pos-1/ℕ (2 , tt)
    ε' = fst ε
    εℝ = ℚ->ℝ ε'
    0<εℝ : 0# < εℝ
    0<εℝ = ℚ->ℝ-preserves-< 0r ε' (Pos-0< ε' (snd ε))
    εℝ<1 : εℝ < 1#
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

        p2 : (x + 0#) == x
        p2 = +-right-zero
      Inv-d->x#y : ℝInv d -> x # y
      Inv-d->x#y (inj-l d<0) = inj-r (subst2 _<_ p1 p2 (+₁-preserves-< d<0))
      Inv-d->x#y (inj-r 0<d) = inj-l (subst2 _<_ p2 p1 (+₁-preserves-< 0<d))

    handle : ((absℝ d < (ℚ->ℝ ε')) ⊎ ℝInv d) ->
             ((absℝ i < (ℚ->ℝ ε')) ⊎ ℝInv i) ->
             x # y
    handle (inj-r inv-d) _ = (Inv-d->x#y inv-d)
    handle (inj-l _) (inj-r inv-i) = (Inv-d->x#y (Inv-i->Inv-d inv-i))
    handle (inj-l ad<ε) (inj-l ai<ε) = bot-elim (εε≮1 εε<1)
      where
      εai≮adai : (εℝ * (absℝ i)) ≮ ((absℝ d) * (absℝ i))
      εai≮adai = *₂-preserves-≮ (asym-< ad<ε) absℝ-≮0

      εε≮εai : (εℝ * εℝ) ≮ (εℝ * (absℝ i))
      εε≮εai = *₁-preserves-≮ (asym-< 0<εℝ) (asym-< ai<ε)

      εε≮adai : (εℝ * εℝ) ≮ ((absℝ d) * (absℝ i))
      εε≮adai = trans-≮ εε≮εai εai≮adai

      0<1ℝ : 0# < 1#
      0<1ℝ = (ℚ->ℝ-preserves-< 0r 1r 0<1)

      adai=1 : ((absℝ d) * (absℝ i)) == 1#
      adai=1 = sym (absℝ-distrib-* d i) >=>
               cong absℝ path >=>
               absℝ-NonNeg-idem 1ℝ (asym-< 0<1ℝ)

      εε≮1 : (εℝ * εℝ) ≮ 1#
      εε≮1 = subst ((εℝ * εℝ) ≮_) adai=1 εε≮adai

      εε<11 : (εℝ * εℝ) < (1# * 1#)
      εε<11 = trans-< (*₁-preserves-< 0<εℝ εℝ<1) (*₂-preserves-< εℝ<1 0<1ℝ)

      εε<1 : (εℝ * εℝ) < 1#
      εε<1 = subst ((εℝ * εℝ) <_) *-right-one εε<11

  ℝ#->diff# : {x y : ℝ} -> x # y -> diff# x y
  ℝ#->diff# {x} {y} x#y = is-unit (ℝ1/ d inv) (*-commute >=> ℝ1/-inverse d inv)
    where
    d = (y + (- x))
    inv : ℝInv d
    inv = ℝ#->ℝInv x y x#y

  abstract
    ℝ#≃diff# : (x y : ℝ) -> (x # y) ≃ (diff# x y)
    ℝ#≃diff# x y = isoToEquiv (isProp->iso ℝ#->diff# diff#->ℝ# isProp-# ℝRing.isProp-isUnit)

private
  +₁-reflects-ℝ< : {a b c : ℝ} -> (a + b) < (a + c) -> b < c
  +₁-reflects-ℝ< {a} ab<ac = subst2 _<_ p p (+₁-preserves-< ab<ac)
    where
    p : {x : ℝ} -> (- a + (a + x)) == x
    p = sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero

  +₂-reflects-ℝ< : {a b c : ℝ} -> (a + c) < (b + c) -> a < b
  +₂-reflects-ℝ< ac<bc = +₁-reflects-ℝ< (subst2 _<_ +-commute +-commute ac<bc)

  +-reflects-ℝ< : {a b c d : ℝ} -> (a + b) < (c + d) -> ∥ (a < c) ⊎ (b < d) ∥
  +-reflects-ℝ< {a} {b} {c} {d} ab<cd = ∥-map handle (comparison-< _ (c + b) _ ab<cd)
    where
    handle : ((a + b) < (c + b)) ⊎ ((c + b) < (c + d)) -> (a < c) ⊎ (b < d)
    handle = ⊎-map +₂-reflects-ℝ< +₁-reflects-ℝ<

instance
  ℝField : Field ℝRing TightApartnessStr-ℝ
  ℝField = record
    { f#-path = (sym (funExt2 (\x y -> (ua (ℝ#≃diff# x y)))))
    }

  abstract
    ApartAdditiveGroup-ℝ : ApartAdditiveGroup AdditiveGroup-ℝ TightApartnessStr-ℝ
    ApartAdditiveGroup-ℝ = record
      { +-reflects-# = +-reflects-ℝ#
      }
      where
      +-reflects-ℝ# : {a b c d : ℝ} -> (a + b) # (c + d) -> ∥ (a # c) ⊎ (b # d) ∥
      +-reflects-ℝ# (inj-l ab<cd) = ∥-map (⊎-map inj-l inj-l) (+-reflects-ℝ< ab<cd)
      +-reflects-ℝ# (inj-r ab>cd) = ∥-map (⊎-map inj-r inj-r) (+-reflects-ℝ< ab>cd)
