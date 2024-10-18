{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.cauchy where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import metric-space
open import metric-space.cauchy
open import metric-space.instances.real
open import nat
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import rational
open import real
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.order
open import real.rational
open import real.sequence.limit
open import real.sequence.rational-cauchy
open import real.subspace
open import sequence
open import subset.subspace
open import truncation

private
  εClose->εBounded : {ε : ℚ} {a b : ℝ} -> distance a b < (ℚ->ℝ ε) -> εBounded ε (diff a b)
  εClose->εBounded dab<ε =
    ℝ<->L (subst2 _<_ (sym ℚ->ℝ-preserves--) minus-double-inverse
                  (minus-flips-< (trans-≤-< max-≤-right dab<ε))) ,
    ℝ<->U (trans-≤-< max-≤-left dab<ε)

  εBounded->εClose : {ε : ℚ} {a b : ℝ} -> εBounded ε (diff a b) -> distance a b < (ℚ->ℝ ε)
  εBounded->εClose (l , u) =
    max-least-< (U->ℝ< u) (trans-<-= (minus-flips-< (L->ℝ< l))
                                     (cong -_ ℚ->ℝ-preserves-- >=> minus-double-inverse))

module _ {s : ℕ -> ℝ} where
  opaque
    isℚCauchy->isCauchy : isℚCauchy s -> isCauchy s
    isℚCauchy->isCauchy cauchy-s (ε , 0<ε) = ∥-bind handle 0<ε
      where
      handle : 0# ℝ<' ε -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> distance (s m₁) (s m₂) < ε)
      handle (ℝ<'-cons εq 0U-εq εL-εq) = ∥-map handle2 (cauchy-s (εq , U->ℚ< 0U-εq))
        where
        handle2 : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εBounded εq (diff (s m₁) (s m₂))) ->
                  Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> distance (s m₁) (s m₂) < ε)
        handle2 (n , f) = (n , \m₁ m₂ n≤m₁ n≤m₂ -> trans-< (εBounded->εClose (f m₁ m₂ n≤m₁ n≤m₂))
                                                           (L->ℝ< εL-εq))

    isCauchy->isℚCauchy : isCauchy s -> isℚCauchy s
    isCauchy->isℚCauchy cauchy-s (ε , 0<ε) = ∥-map handle (cauchy-s (ℚ->ℝ ε , ℚ->ℝ-preserves-< 0<ε))
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> distance (s m₁) (s m₂) < ℚ->ℝ ε) ->
               Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εBounded ε (diff (s m₁) (s m₂)))
      handle (n , f) = n , (\m₁ m₂ n≤m₁ n≤m₂ -> εClose->εBounded (f m₁ m₂ n≤m₁ n≤m₂))


    isCauchy'->isℚCauchy' : isCauchy' s -> isℚCauchy' s
    isCauchy'->isℚCauchy' close (ε , 0<ε) =
      ∀Largeℕ-map handle (close εℝ⁺)
      where
      εℝ⁺ : ℝ⁺
      εℝ⁺ = ℚ->ℝ ε , ℚ->ℝ-preserves-< 0<ε
      handle : {i : ℕ} -> ((j : ℕ) -> i ≤ j -> εClose εℝ⁺ (s i) (s j)) ->
                          ((j : ℕ) -> i ≤ j -> εBounded ε (diff (s i) (s j)))
      handle bound j i≤j = εClose->εBounded (bound j i≤j)

opaque
  isConvergentSequence->isCauchy : {s : Sequence ℝ} -> isConvergentSequence s -> isCauchy s
  isConvergentSequence->isCauchy = isℚCauchy->isCauchy ∘ isConvergentSequence->isℚCauchy

  isCauchy->isConvergentSequence : {s : Sequence ℝ} -> isCauchy s -> isConvergentSequence s
  isCauchy->isConvergentSequence = isℚCauchy->isConvergentSequence ∘ isCauchy->isℚCauchy
