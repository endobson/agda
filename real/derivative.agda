{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import hlevel
open import order.instances.real
open import real
open import real.arithmetic.multiplication.inverse
open import real.sequence.limit-point
open import relation
open import ring.implementations.real
open import semiring
open import sigma.base

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

isProp-ΣisDerivative : {f : ℝ -> ℝ} -> isProp (Σ (ℝ -> ℝ) (isDerivative f))
isProp-ΣisDerivative {f} (f'1 , isDer1) (f'2 , isDer2) =
  ΣProp-path isProp-isDerivative (funExt f'1=f'2)
  where
  f'1=f'2 : (x : ℝ) -> f'1 x == f'2 x
  f'1=f'2 x = cong fst (isProp-ΣisLimitAt d1 d2)
    where
    d1 : Σ ℝ (isDerivativeAt f x)
    d1 = f'1 x , isDer1 x
    d2 : Σ ℝ (isDerivativeAt f x)
    d2 = f'2 x , isDer2 x
