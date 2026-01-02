{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.taylor-series where

open import additive-group
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import equality
open import heyting-field.instances.real
open import nat
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.exponential-series
open import real.series
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import truncation

alt-coeff : ℝ -> ℝ -> ℕ -> ℝ
alt-coeff a b zero    = a
alt-coeff a b (suc n) = alt-coeff b (- a) n

sin-alt-coeff : ℕ -> ℝ
sin-alt-coeff = alt-coeff 0# 1#

sin-coeff : ℕ -> ℝ
sin-coeff n = sin-alt-coeff n * 1/ℕ (factorial⁺ n)

sin-terms : ℝ -> ℕ -> ℝ
sin-terms x n = sin-coeff n * (x ^ℕ n)

cos-alt-coeff : ℕ -> ℝ
cos-alt-coeff = alt-coeff 1# 0#

cos-coeff : ℕ -> ℝ
cos-coeff n = cos-alt-coeff n * 1/ℕ (factorial⁺ n)

cos-terms : ℝ -> ℕ -> ℝ
cos-terms x n = cos-coeff n * (x ^ℕ n)

exp-coeff : ℕ -> ℝ
exp-coeff n = 1/ℕ (factorial⁺ n)

-- 'exp-terms' is defined with the exponential. This checks that it is as expected.
module _ where
  private
    exp-terms' : ℝ -> ℕ -> ℝ
    exp-terms' x n = exp-coeff n * (x ^ℕ n)

    check-exp-terms : exp-terms == exp-terms'
    check-exp-terms = refl


abs-sin-alt-coeff≤1 : ∀ (n : Nat) -> abs (sin-alt-coeff n) ≤ 1#
abs-sin-alt-coeff≤1 zero       = trans-=-≤ (abs-0≤-path refl-≤) 0≤1
abs-sin-alt-coeff≤1 (suc zero) = trans-=-≤ (abs-0≤-path 0≤1) refl-≤
abs-sin-alt-coeff≤1 (suc (suc zero)) = trans-=-≤ (abs-minus >=> abs-0≤-path refl-≤) 0≤1
abs-sin-alt-coeff≤1 (suc (suc (suc zero))) =
  trans-=-≤ abs-minus (path-≤ (abs-0≤-path 0≤1))
abs-sin-alt-coeff≤1 (suc (suc (suc (suc n)))) =
  subst2 (\x1 x2 -> abs (alt-coeff x1 x2 n) ≤ 1#)
         (sym minus-double-inverse)
         (sym minus-double-inverse)
         (abs-sin-alt-coeff≤1 n)

abs-cos-alt-coeff≤1 : ∀ (n : Nat) -> abs (cos-alt-coeff n) ≤ 1#
abs-cos-alt-coeff≤1 n = trans-=-≤ (cong abs (cong (\z -> alt-coeff 1# z n) (sym minus-zero)))
                                  (abs-sin-alt-coeff≤1 (suc n))

module _ (x : ℝ) where
  opaque
    isAbsConvergentSeries-cos : isAbsConvergentSeries (cos-terms x)
    isAbsConvergentSeries-cos =
      squeeze-isAbsConvergentSeries
        ∣ (0 , \n _ -> acos-terms≤aexp-terms n) ∣
        (isAbsConvergentSeries-exponential x)
      where

      acos-coeff≤aexp-coeff : ∀ n -> abs (cos-coeff n) ≤ abs (exp-coeff n)
      acos-coeff≤aexp-coeff n =
       subst2 _≤_ (sym abs-distrib-*) *-left-one
         (*₂-preserves-≤ (abs-cos-alt-coeff≤1 n) abs-0≤)

      acos-terms≤aexp-terms : ∀ n -> abs (cos-terms x n) ≤ abs (exp-terms x n)
      acos-terms≤aexp-terms n =
       subst2 _≤_ (sym abs-distrib-*) (sym abs-distrib-*)
         (*₂-preserves-≤ (acos-coeff≤aexp-coeff n) abs-0≤)

    isAbsConvergentSeries-sin : isAbsConvergentSeries (sin-terms x)
    isAbsConvergentSeries-sin =
      squeeze-isAbsConvergentSeries
        ∣ (0 , \n _ -> asin-terms≤aexp-terms n) ∣
        (isAbsConvergentSeries-exponential x)
      where

      asin-coeff≤aexp-coeff : ∀ n -> abs (sin-coeff n) ≤ abs (exp-coeff n)
      asin-coeff≤aexp-coeff n =
       subst2 _≤_ (sym abs-distrib-*) *-left-one
         (*₂-preserves-≤ (abs-sin-alt-coeff≤1 n) abs-0≤)

      asin-terms≤aexp-terms : ∀ n -> abs (sin-terms x n) ≤ abs (exp-terms x n)
      asin-terms≤aexp-terms n =
       subst2 _≤_ (sym abs-distrib-*) (sym abs-distrib-*)
         (*₂-preserves-≤ (asin-coeff≤aexp-coeff n) abs-0≤)
