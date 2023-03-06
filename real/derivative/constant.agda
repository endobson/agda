{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative.constant where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import integral-domain
open import order.instances.real
open import ordered-integral-domain
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.derivative
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation

private
  module _ (k : ℝ) where
    const : ℝ -> ℝ 
    const _ = k
  
    isDerivativeAt-const : (x : ℝ) -> isDerivativeAt const x 0#
    isDerivativeAt-const x .isLimitAt.limit-point = ∣ lim-point ∣
      where
      lim-point : isLimitPoint' (\h -> h # 0# , isProp-#) 0#
      lim-point .isLimitPoint'.seq n = ℚ->ℝ (1/ℕ (suc n , tt))
      lim-point .isLimitPoint'.S-seq n = 
        inj-r (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _))
      lim-point .isLimitPoint'.seq-#x n = 
        inj-r (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _))
      lim-point .isLimitPoint'.isLimit-seq = isLimit-harmonic-sequence
    isDerivativeAt-const x .isLimitAt.δε δ = ∣ (1# , 0<1) , g ∣
      where
      g : (z : ℝ) -> εBounded 1# (diff z 0#) -> (z#0 : z # 0#) -> 
          εBounded ⟨ δ ⟩ (diff (rise-over-run const x (z , z#0)) 0#)
      g z _ z#0 = subst (εBounded ⟨ δ ⟩) (sym d=0) (εBounded-zero δ)
        where
        d=0 : (diff (rise-over-run const x (z , z#0)) 0#) == 0#
        d=0 = 
          +-left-zero >=>
          cong -_ (*-left +-inverse >=> *-left-zero) >=>
          minus-zero

isDerivative-const : (k : ℝ) -> isDerivative (const k) (const 0#)
isDerivative-const k = isDerivativeAt-const k

