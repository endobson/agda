{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.ball-subspace where

open import base
open import metric-space
open import order
open import order.instances.real
open import real.subspace
open import subset
open import subset.subspace

module _ {ℓA : Level} {A : Type ℓA} {{MS-A : MetricSpaceStr A}} where

  εBallAtS : (ε : ℝ⁺) (a : A) -> Subtype A _
  εBallAtS ε a₀ a = εClose ε a₀ a , isProp-<

  εBallAt : (ε : ℝ⁺) (a : A) -> Type (ℓ-max ℓA ℓ-one)
  εBallAt ε a = Subspace (εBallAtS ε a)
