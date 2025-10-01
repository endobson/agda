{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.descending-factorial where

open import nat
open import equality-path
open import base
open import additive-group
open import semiring
open import order
open import order.instances.nat
open import combinatorics.factorial
open import combinatorics.binomial-coefficients
open import combinatorics.properties.binomial-coefficients-factorial
open import semiring.instances.nat
open import additive-group.instances.nat

falling-factorial : ℕ -> ℕ -> ℕ
falling-factorial n zero = 1#
falling-factorial zero (suc n) = 0#
falling-factorial (suc n) (suc k) =
  (suc n) * (falling-factorial n k)

falling-factorial-one₂ : (n : ℕ) -> falling-factorial n 1 == n
falling-factorial-one₂ zero = refl
falling-factorial-one₂ (suc n) = *-right-one

falling-factorial-same : ∀ n -> falling-factorial n n == factorial n
falling-factorial-same zero = refl
falling-factorial-same (suc n) = cong (suc n *_) (falling-factorial-same n)


falling-factorial-factorial-path : ∀ k n ->
  falling-factorial (k + n) k * factorial n == factorial (k + n)
falling-factorial-factorial-path zero n = *-left-one
falling-factorial-factorial-path (suc k) n =
  *-assocᵉ (suc k + n) (falling-factorial (k + n) k) (factorial n) >=>
  cong ((suc k + n) *_) (falling-factorial-factorial-path k n)


falling-factorial-binom-coeff'-path : ∀ k n ->
  falling-factorial (k + n) k == binomial-coeff' n k * factorial k
falling-factorial-binom-coeff'-path k n =
  *'-right-injective (factorial⁺ n)
    (falling-factorial-factorial-path k n >=>
     sym (binomial-coeff'-factorial-path k n) >=>
     *-left (sym-binomial-coeff' k n) >=>
     sym (*-assocᵉ (binomial-coeff' n k) (factorial k) (factorial n)))
