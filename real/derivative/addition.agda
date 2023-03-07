{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative.addition where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import integral-domain
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import ordered-integral-domain
open import ordered-semiring
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative
open import real.epsilon-bounded
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation

isDerivative-+ : {f f' g g' : ℝ -> ℝ} -> isDerivative f f' -> isDerivative g g' ->
                 isDerivative (\x -> f x + g x) (\x -> f' x + g' x)
isDerivative-+ isD-f isD-g x .isLimitAt.limit-point = ∣ lim-point ∣
  where
  lim-point : isLimitPoint' (\h -> h # 0# , isProp-#) 0#
  lim-point .isLimitPoint'.seq n = ℚ->ℝ (1/ℕ (suc n , tt))
  lim-point .isLimitPoint'.S-seq n =
    inj-r (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _))
  lim-point .isLimitPoint'.seq-#x n =
    inj-r (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _))
  lim-point .isLimitPoint'.isLimit-seq = isLimit-harmonic-sequence
isDerivative-+ {f} {f'} {g} {g'} isD-f isD-g x .isLimitAt.δε δ =
  ∥-map2 handle (isD-f x .isLimitAt.δε δ/2) (isD-g x .isLimitAt.δε δ/2)
  where
  δ/2 : ℚ⁺
  δ/2 = 1/2r * fst δ , *-preserves-0< Pos-1/2r (snd δ)
  fg = \x -> f x + g x
  handle : Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z 0#) ->
                        (sz : z # 0#) -> εBounded ⟨ δ/2 ⟩ (diff (rise-over-run f x (z , sz)) (f' x))) ->
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z 0#) ->
                        (sz : z # 0#) -> εBounded ⟨ δ/2 ⟩ (diff (rise-over-run g x (z , sz)) (g' x))) ->
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z 0#) ->
                        (sz : z # 0#) -> εBounded ⟨ δ ⟩ (diff (rise-over-run fg x (z , sz)) (f' x + g' x)))
  handle ((εf , 0<εf) , bf) ((εg , 0<εg) , bg) = (εfg , 0<εfg) , bfg
    where
    εfg = min εf εg
    0<εfg = min-property εf εg 0<εf 0<εg
    bfg : (z : ℝ) -> εBounded εfg (diff z 0#) ->
          (sz : z # 0#) -> εBounded ⟨ δ ⟩ (diff (rise-over-run fg x (z , sz)) (f' x + g' x))
    bfg z εfg-dz z#0 =
      subst2 εBounded (1/2r-path' ⟨ δ ⟩) ror-path (εBounded-+ _ _ δ/2-ror-f δ/2-ror-g)
      where
      dz = diff z 0#
      εf-dz = weaken-εBounded min-≤-left dz εfg-dz
      εg-dz = weaken-εBounded min-≤-right dz εfg-dz
      δ/2-ror-f = bf z εf-dz z#0
      δ/2-ror-g = bg z εg-dz z#0
      ror-path : (diff (rise-over-run f x (z , z#0)) (f' x)) +
                 (diff (rise-over-run g x (z , z#0)) (g' x)) ==
                 (diff (rise-over-run fg x (z , z#0)) (f' x + g' x))
      ror-path =
        +-swap-diff >=>
        +-right (cong -_ (sym *-distrib-+-right >=>
                          *-left +-swap-diff))
