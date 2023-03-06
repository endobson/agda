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
open import rational.proper-interval
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.multiplication
open import real.arithmetic.order
open import real.rational
open import real.interval
open import real.epsilon-bounded.base
open import relation
open import ring.implementations.real
open import semiring
open import sum
open import truncation


private
  open ℝRing using (is-unit)

  εBounded->0<ε : {ε : ℚ} (x : ℝ) -> εBounded ε x -> 0# < ε
  εBounded->0<ε {ε} x (-ε<x , x<ε) = proj-¬r (split-< 0# ε) ¬ε≤0
    where
    -ε<ε : ℚ->ℝ (- ε) < ℚ->ℝ ε
    -ε<ε = trans-< (L->ℝ< {x = x} -ε<x) (U->ℝ< x<ε)
    ¬ε≤0 : ¬ (ε ≤ 0#)
    ¬ε≤0 ε≤0 = irrefl-< (trans-<-≤ -ε<ε (ℚ->ℝ-preserves-≤ _ _ (trans-≤ ε≤0 (minus-flips-≤0 ε≤0))))


  εBounded->Iℚ : {ε : ℚ} (x : ℝ) -> εBounded ε x -> Iℚ
  εBounded->Iℚ {ε} x εB = Iℚ-cons (- ε) ε (weaken-< (trans-< (minus-flips-0< 0<ε) 0<ε))
    where
    0<ε : 0# < ε
    0<ε = (εBounded->0<ε x εB)

  εBounded->ℝ∈Iℚ : {ε : ℚ} (x : ℝ) -> (εB : εBounded ε x) -> ℝ∈Iℚ x (εBounded->Iℚ x εB)
  εBounded->ℝ∈Iℚ x εB = εB

  εBounded-* : {ε1 ε2 : ℚ} (x y : ℝ) -> εBounded ε1 x -> εBounded ε2 y -> εBounded (ε1 * ε2) (x * y)
  εBounded-* {ε1} {ε2} x y ε1-x ε2-y =
    subst (ℝ∈Iℚ (x * y)) (sym (i*-SymI-path iε1 iε2 refl refl)) ℝ∈Iℚ-xy
    where
    iε1 : Iℚ
    iε1 = εBounded->Iℚ x ε1-x
    iε2 : Iℚ
    iε2 = εBounded->Iℚ y ε2-y
    ℝ∈Iℚ-xy : ℝ∈Iℚ (x * y) (iε1 i* iε2)
    ℝ∈Iℚ-xy = ℝ∈Iℚ-* x y iε1 iε2 (εBounded->ℝ∈Iℚ x ε1-x) (εBounded->ℝ∈Iℚ y ε2-y)



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
