{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative.identity where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation


private
  id : ℝ -> ℝ
  id x = x

isDerivative-id : isDerivative id (\_ -> 1#)
isDerivative-id = isDerivative-cons handle
  where
  module _ (x : ℝ) (δ : ℚ⁺) where
    g : (z : ℝ) -> εBounded 1# z -> (z#0 : z # 0#) ->
        εBounded ⟨ δ ⟩ (diff (rise-over-run id x (z , z#0)) 1#)
    g z _ z#0 = subst (εBounded ⟨ δ ⟩) (sym d=0) (εBounded-zero δ)
      where
      d=0 : (diff (rise-over-run id x (z , z#0)) 1#) == 0#
      d=0 =
        +-right (cong -_ (*-left (+-left +-commute >=> +-assoc >=>
                                  +-right +-inverse >=> +-right-zero) >=>
                          *-commute >=> ℝ1/-inverse z z#0)) >=>
        +-inverse
    handle : _
    handle = ∣ (1# , 0<1) , g ∣
