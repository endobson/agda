{-# OPTIONS --cubical --safe --exact-split #-}

module real.apartness where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import isomorphism
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.order
open import real.epsilon-bounded
open import real.interval
open import real.rational
open import relation
open import ring.implementations.real
open import semiring
open import truncation


private
  open ℝRing using (is-unit)


  split-small-inv : (x : ℝ) -> (ε : ℚ⁺) -> ∥ (εBounded ⟨ ε ⟩ x) ⊎ ℝInv x ∥
  split-small-inv x ε⁺@(ε , _) = ∥-map handle (trichotomous-εBounded ε⁺ x)
    where
    handle : Tri⊎ (x < 0#) (εBounded ε x) (0# < x) -> (εBounded ε x) ⊎ ℝInv x
    handle (tri⊎-< x<0) = inj-r (inj-l x<0)
    handle (tri⊎-= εB)  = inj-l εB
    handle (tri⊎-> x>0) = inj-r (inj-r x>0)


  diff# : ℝ -> ℝ -> Type _
  diff# x y = ℝRing.isUnit (diff x y)

  diff#->ℝ# : {x y : ℝ} -> diff# x y -> x # y
  diff#->ℝ# {x} {y} (is-unit i path) =
    unsquash isProp-# (∥-map2 handle (split-small-inv d ε) (split-small-inv i ε))
    where
    ε' = 1/2r
    0<ε : 0# < ε'
    0<ε = Pos-1/ℕ (2 , tt)
    ε<1 : ε' < 1#
    ε<1 = 1/2r<1r
    ε : ℚ⁺
    ε = ε' , 0<ε

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

    handle : ((εBounded ε' d) ⊎ ℝInv d) ->
             ((εBounded ε' i) ⊎ ℝInv i) ->
             x # y
    handle (inj-r inv-d) _             = (Inv-d->x#y inv-d)
    handle (inj-l _)     (inj-r inv-i) = (Inv-d->x#y (Inv-i->Inv-d inv-i))
    handle (inj-l ε-d)   (inj-l ε-i)   = bot-elim (asym-< 1<ε² ε²<1)
      where
      ε-di : εBounded (ε' * ε') (d * i)
      ε-di = εBounded-* d i ε-d ε-i

      U1-ε² : Real.U 1# (ε' * ε')
      U1-ε² = proj₂ (subst (εBounded (ε' * ε')) path ε-di)

      1<ε² : 1# < (ε' * ε')
      1<ε² = U->ℚ< U1-ε²

      ε²<1 : (ε' * ε') < 1#
      ε²<1 = trans-< (*₁-preserves-< 0<ε ε<1) (trans-=-< *-right-one ε<1)


  ℝ#->diff# : {x y : ℝ} -> x # y -> diff# x y
  ℝ#->diff# {x} {y} x#y = is-unit (ℝ1/ d inv) (*-commute >=> ℝ1/-inverse d inv)
    where
    d = (y + (- x))
    inv : ℝInv d
    inv = ℝ#->ℝInv x y x#y

abstract
  ℝ#≃diff# : (x y : ℝ) -> (x # y) ≃ (diff# x y)
  ℝ#≃diff# x y = isoToEquiv (isProp->iso ℝ#->diff# diff#->ℝ# isProp-# ℝRing.isProp-isUnit)
