{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import hlevel
open import real
open import real.arithmetic.multiplication.inverse
open import real.order
open import real.sequence.limit-point
open import relation
open import ring.implementations.real
open import semiring

-- Rise over run at point x with distance h
rise-over-run : (f : ℝ -> ℝ) (x : ℝ) (h : Σ ℝ (_# 0#)) -> ℝ
rise-over-run f x (h , h#0) = diff (f x) (f (x + h)) * ℝ1/ h h#0

isDerivativeAt : (f : ℝ -> ℝ) (x : ℝ) (d : ℝ) -> Type₁
isDerivativeAt f x d = isLimitAt (\h -> h # 0# , isProp-#) (rise-over-run f x) 0# d

isDerivative : Rel (ℝ -> ℝ) ℓ-one
isDerivative f f' = (x : ℝ) -> isDerivativeAt f x (f' x)

isProp-isDerivative : {f f' : ℝ -> ℝ} -> isProp (isDerivative f f')
isProp-isDerivative = 
  isPropΠ (\_ -> isProp-isLimitAt)
