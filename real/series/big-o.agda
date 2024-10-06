{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.big-o where

open import additive-group.instances.real
open import base
open import equality
open import finset.instances
open import finsum.arithmetic
open import funext
open import nat
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-semiring.big-o
open import real
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.series
open import ring.implementations.real
open import semiring
open import subset.subspace
open import truncation

opaque
  isConvergentSeries-BigO : {f g : ℕ -> ℝ} ->
    BigO f g -> isConvergentSeries g -> isConvergentSeries f
  isConvergentSeries-BigO {f} {g} f∈g (lim-g , isLim-g) =
    unsquash isProp-isConvergentSeries (∥-map handle f∈g)
    where
    handle : BigO' f g -> isConvergentSeries f
    handle ((k , _) , N , af≤kg) =
      squeeze-abs-isConvergentSeries (∣ N , af≤kg ∣) conv-kg
      where
      conv-kg : isConvergentSeries (\i -> k * g i)
      conv-kg =
        k * lim-g ,
        subst2 isLimit (funExt (\n -> sym finiteSum-*)) refl
          (*₁-preserves-limit isLim-g)
