{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.rational where

open import additive-group
open import additive-group.instances.real
open import equality
open import base
open import rational
open import rational.proper-interval
open import real
open import real.rational
open import order
open import order.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-ring
open import real.arithmetic
open import real.interval
open import truncation


ℚ->ℝ-preserves-+ : {q r : ℚ} -> ℚ->ℝ (q + r) == ℚ->ℝ q + ℚ->ℝ r
ℚ->ℝ-preserves-+ {q} {r} = sym (ℝ∈Iℚ->path _ _ f) >=> sym ℝ+-eval
  where
  module q = Real (ℚ->ℝ q)
  module r = Real (ℚ->ℝ r)
  s = ((ℚ->ℝ q) ℝ+ᵉ (ℚ->ℝ r))
  module s = Real s

  f : (qi : Iℚ) -> ℝ∈Iℚ s qi -> ℝ∈Iℚ (ℚ->ℝ (q + r)) qi
  f qi@(Iℚ-cons l u _) (sL-l , sU-u) =
    unsquash (isProp-ℝ∈Iℚ (ℚ->ℝ (q + r)) qi) (∥-map2 handle sL-l sU-u)
    where
    handle : Σ[ lq ∈ ℚ ] Σ[ lr ∈ ℚ ] (q.L lq × r.L lr × lq + lr == l) ->
             Σ[ uq ∈ ℚ ] Σ[ ur ∈ ℚ ] (q.U uq × r.U ur × uq + ur == u) ->
             ℝ∈Iℚ (ℚ->ℝ (q + r)) qi
    handle (lq , lr , L-lq , L-lr , lq+lr=l) (uq , ur , U-uq , U-ur , uq+ur=u) =
      ℚ<->L (subst2 _<_ lq+lr=l refl (+-preserves-< (L->ℚ< L-lq) (L->ℚ< L-lr))) ,
      ℚ<->U (subst2 _<_ refl uq+ur=u (+-preserves-< (U->ℚ< U-uq) (U->ℚ< U-ur)))

ℚ->ℝ-preserves-- : {q : ℚ} -> ℚ->ℝ (- q) == - (ℚ->ℝ q)
ℚ->ℝ-preserves-- {q} = sym (ℝ∈Iℚ->path _ _ f) >=> sym ℝ--eval
  where
  f : (qi : Iℚ) -> ℝ∈Iℚ (ℝ-ᵉ (ℚ->ℝ q)) qi -> ℝ∈Iℚ (ℚ->ℝ (- q)) qi
  f (Iℚ-cons l u _) (U-ml , L-mu) = L-case , U-case
    where
    L-case : Real.L (ℚ->ℝ (- q)) l
    L-case = ℚ<->L (subst2 _<_ minus-double-inverse refl (minus-flips-< (U->ℚ< U-ml)))
    U-case : Real.U (ℚ->ℝ (- q)) u
    U-case = ℚ<->U (subst2 _<_ refl minus-double-inverse (minus-flips-< (L->ℚ< L-mu)))
