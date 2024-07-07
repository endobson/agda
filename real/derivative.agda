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
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded.base
open import real.epsilon-bounded
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit-point
open import relation
open import ring.implementations.real
open import semiring
open import sigma.base
open import subset.subspace
open import truncation

-- Rise over run at point x with distance h
rise-over-run : (f : ℝ -> ℝ) (x : ℝ) (h : Σ ℝ (_# 0#)) -> ℝ
rise-over-run f x (h , h#0) = diff (f x) (f (x + h)) * ℝ1/ (h , h#0)

isDerivativeAt : (f : ℝ -> ℝ) (x : ℝ) (d : ℝ) -> Type₁
isDerivativeAt f x d = isLimitAt (\h -> h # 0# , isProp-#) (rise-over-run f x) 0# d

isDerivative : Rel (ℝ -> ℝ) ℓ-one
isDerivative f f' = (x : ℝ) -> isDerivativeAt f x (f' x)

opaque
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

  isDerivative-cons :
    {f : ℝ -> ℝ} {d : ℝ -> ℝ} ->
    (δε : (x : ℝ) -> (δ : ℚ⁺) -> ∃[ ε ∈ ℚ⁺ ]
      ((z : ℝ) -> εBounded ⟨ ε ⟩ z ->
       (z#0 : z # 0#) -> εBounded ⟨ δ ⟩ (diff (rise-over-run f x (z , z#0)) (d x)))) ->
    isDerivative f d
  isDerivative-cons {f} {d} δε x = isDerivativeAt-cons (d x) (δε x)
    where
    isDerivativeAt-cons :
      (d : ℝ) ->
      (δε : (δ : ℚ⁺) -> ∃[ ε ∈ ℚ⁺ ]
        ((z : ℝ) -> εBounded ⟨ ε ⟩ z ->
         (z#0 : z # 0#) -> εBounded ⟨ δ ⟩ (diff (rise-over-run f x (z , z#0)) d))) ->
      isDerivativeAt f x d
    isDerivativeAt-cons d δε .isLimitAt.δε = δε'
      where
      δε' : (δ : ℚ⁺) -> ∃[ ε ∈ ℚ⁺ ]
               ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z 0#) ->
                (z#0 : z # 0#) -> εBounded ⟨ δ ⟩ (diff (rise-over-run f x (z , z#0)) d))
      δε' δ = ∥-map (\ (ε , f) -> (ε , (\ z zb -> f z (bound-convert z zb)))) (δε δ)
        where
        bound-convert : {ε : ℚ} -> (z : ℝ) -> εBounded ε (diff z 0#) -> εBounded ε z
        bound-convert {ε} z zb = subst (εBounded ε) bound-path (εBounded-- (diff z 0#) zb)
          where
          bound-path : - (diff z 0#) == z
          bound-path = sym diff-anticommute >=> sym +-left-zero >=> diff-step
    isDerivativeAt-cons d δε .isLimitAt.limit-point = 0-lim-point
      where
      0-lim-point : isLimitPoint (\x -> x # 0# , isProp-#) 0#
      0-lim-point = ∣ lim-point ∣
        where
        lim-point : isLimitPoint' (\h -> h # 0# , isProp-#) 0#
        lim-point .isLimitPoint'.seq = harmonic-sequence
        lim-point .isLimitPoint'.S-seq n = inj-r (0<harmonic-sequence n)
        lim-point .isLimitPoint'.seq-#x n = inj-r (0<harmonic-sequence n)
        lim-point .isLimitPoint'.isLimit-seq = isLimit-harmonic-sequence
