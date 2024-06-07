{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative.constant where

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
open import real.derivative
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation

private
  const : ℝ -> ℝ -> ℝ
  const k _ = k

module _ (k : ℝ) where
  isDerivative-const : isDerivative (const k) (const 0#)
  isDerivative-const = isDerivative-cons handle
    where
    module _ (x : ℝ) (δ : ℚ⁺) where
      g : (z : ℝ) -> εBounded 1# (diff z 0#) -> (z#0 : z # 0#) ->
          εBounded ⟨ δ ⟩ (diff (rise-over-run (const k) x (z , z#0)) 0#)
      g z _ z#0 = subst (εBounded ⟨ δ ⟩) (sym d=0) (εBounded-zero δ)
        where
        d=0 : (diff (rise-over-run (const k) x (z , z#0)) 0#) == 0#
        d=0 =
          +-left-zero >=>
          cong -_ (*-left +-inverse >=> *-left-zero) >=>
          minus-zero

      handle : _
      handle = ∣ (1# , 0<1) , g ∣
