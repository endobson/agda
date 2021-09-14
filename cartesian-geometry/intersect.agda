{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.intersect where

open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import functions
open import real.heyting-field
open import heyting-field
open import real
open import order
open import real.arithmetic.absolute-value
open import ring
open import semiring
open import ring.implementations.real
open import cartesian-geometry.vector
open import vector-space.finite
open import isomorphism
open import integral-domain
open import integral-domain.instances.real

private
  direction->run/rise : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# -> ℝ
  direction->run/rise d@(dv , _) abs-d#axis =
    (vector-index dv x-axis) * (Ring.isUnit.inv isUnit-y)
    where
    d#axis : (basis-decomposition (isBasis-rotated-basis d) xaxis-vector y-axis) # 0#
    d#axis = (eqFun (<>-equiv-# _ _) (absℝ-#0 _ (eqInv (<>-equiv-# _ _) abs-d#axis)))

    d-path : (basis-decomposition (isBasis-rotated-basis d) xaxis-vector) ==
             (vector-index ⟨ (conjugate-direction d) ⟩ )
    d-path = cong vector-index (rotated-basis-x-axis (conjugate-direction d))

    d#axis2 : (- (vector-index dv y-axis)) # 0#
    d#axis2 = subst (\x -> x y-axis # 0#) d-path d#axis

    d#axis3 : (vector-index dv y-axis) # 0#
    d#axis3 = subst2 _#_ minus-double-inverse minus-zero (minus-reflects-# d#axis2)

    isUnit-y : Ring.isUnit ℝRing (vector-index dv y-axis)
    isUnit-y = Field.#0->isUnit ℝField d#axis3
