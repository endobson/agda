{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.spheres.connected where

open import pointed.spheres
open import pointed.suspension
open import connected
open import suspension.connected
open import base
open import truncation.generic


Inhabited->isConnected₋₁ : {ℓ : Level} {A : Type ℓ} -> A -> isConnected₋₁ A
Inhabited->isConnected₋₁ a = ∣ a ∣ , isOfHLevel-Squashₙ 1 _

isConnected-Sₙ : (n : Nat) -> isConnectedₙ₋₂ (suc n) (Sⁿ n)
isConnected-Sₙ 0 = Inhabited->isConnected₋₁ north
isConnected-Sₙ (suc n) = isConnected-Susp (isConnected-Sₙ n)
