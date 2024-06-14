{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.chain-rule where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import heyting-field.instances.rational
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group.instances.rational
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative2
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.epsilon-bounded
open import real.rational
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation
open import subset
open import sequence
open import funext


module _ {ℓS1 ℓS2 : Level} (S1 : Subtype ℝ ℓS1) (S2 : Subtype ℝ ℓS2)
         {f f' : ∈-Subtype S2 -> ℝ} {g g' : ∈-Subtype S1 -> ℝ}
         (Sg : ∀ (x : ∈-Subtype S1) -> ⟨ S2 (g x) ⟩)
         (df : isDerivative S2 f f') (dg : isDerivative S1 g g') where

  private
    g∈ : ∈-Subtype S1 -> ∈-Subtype S2
    g∈ x = g x , Sg x

  -- isDerivative-∘ : isDerivative S1 (\x -> f (g∈ x)) (\x -> f' (g∈ x) * g' x)
  -- isDerivative-∘ = ?

--   isDerivative (UnivS ℝ) (\(x , _) -> x ^ℕ n) (\(x , _) -> ℕ->ℝ n * x ^ℕ (pred n))
-- isDerivative-∘^ℕ zero =
