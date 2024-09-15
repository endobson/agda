{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.plus where

open import additive-group
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import combinatorics.properties.binomial-coefficients-factorial
open import equality
open import fin.sum-pair
open import finset.instances.sum-pair
open import finsum
open import finsum.arithmetic
open import funext
open import heyting-field.instances.real
open import nat
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring.instances.real
open import real
open import real.exponential-series
open import real.exponential.zero
open import real.sequence.limit
open import real.series.cauchy-product
open import ring.implementations.real
open import semiring
open import semiring.exponentiation.binomial-expansion
open import semiring.initial
open import sequence.partial-sums
open import truncation

module _ (x y : ℝ) where
  opaque
    exp-+-path : exp (x + y) == exp x * exp y
    exp-+-path =
      cong fst (isProp-isConvergentSequence (exp (x + y) , lim1)
                                            (exp x * exp y , lim2))
      where
      p1 : ∀ n -> exp-terms (x + y) n ==
                  (cauchy-product (exp-terms x) (exp-terms y) n)
      p1 n =
        *-right (binomial-expansion-path x y n) >=>
        sym finiteSum-* >=>
        cong finiteSum (funExt \(fin-pair+ i j i+j=n) ->
          sym *-assoc >=>
          *-left (
            sym *-right-one >=>
            *-right (sym (∃!-prop (∃!1/ℕ (factorial⁺ i *⁺ factorial⁺ j)))) >=>
            *-left *-commute >=>
            *-swap >=>
            *-left (sym (Semiringʰ.preserves-* (∃!-prop ∃!ℕ->Semiring) _ _) >=>
                    cong ℕ->Semiring (binomial-coeff'-factorial-path i j >=>
                                      cong factorial i+j=n)) >=>
            sym *-assoc >=>
            *-left (∃!-prop (∃!1/ℕ (factorial⁺ n))) >=>
            *-left-one >=>
            1/ℕ-distrib-* (factorial⁺ i) (factorial⁺ j)) >=>
          *-swap)

      lim1 : isLimit (partial-sums (cauchy-product (exp-terms x) (exp-terms y)))
                     (exp (x + y))
      lim1 =
        subst2 isLimit (funExt (\n -> cong (\f -> partial-sums f n) (funExt p1))) refl
          (isLimit-exp (x + y))

      lim2 : isLimit (partial-sums (cauchy-product (exp-terms x) (exp-terms y)))
                     (exp x * exp y)
      lim2 = isLimit-cauchy-product (isLimit-exp x) (isLimit-exp y)
                                    (isAbsConvergentSeries-exponential x)
opaque
  exp-minus-inverse : {x : ℝ} -> exp x * exp (- x) == 1#
  exp-minus-inverse {x} =
    sym (exp-+-path x (- x)) >=>
    cong exp +-inverse >=>
    exp0-path
