{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.binomial-coefficients where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import nat
open import semiring
open import semiring.instances.nat

-- (n + k) C k
binomial-coeff' : ℕ -> ℕ -> ℕ
binomial-coeff' zero k = 1#
binomial-coeff' (suc n) zero = 1#
binomial-coeff' (suc n) (suc k) =
  binomial-coeff' n (suc k) +
  binomial-coeff' (suc n) k

binomial-coeff'-zero₁ : (j : ℕ) -> binomial-coeff' zero j == 1#
binomial-coeff'-zero₁ _ = refl
binomial-coeff'-zero₂ : (i : ℕ) -> binomial-coeff' i zero == 1#
binomial-coeff'-zero₂ zero = refl
binomial-coeff'-zero₂ (suc i) = refl

sym-binomial-coeff' : (n k : ℕ) -> binomial-coeff' n k == binomial-coeff' k n
sym-binomial-coeff' zero zero = refl
sym-binomial-coeff' zero (suc k) = refl
sym-binomial-coeff' (suc n) zero = refl
sym-binomial-coeff' (suc n) (suc k) =
  +-commuteᵉ (binomial-coeff' n (suc k)) (binomial-coeff' (suc n) k) >=>
  +-cong (sym-binomial-coeff' (suc n) k) (sym-binomial-coeff' n (suc k))
