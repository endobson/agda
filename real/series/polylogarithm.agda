{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.polylogarithm where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import fin.sum-pair
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import finsum.arithmetic
open import finsum.cardinality
open import functions
open import funext
open import nat
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.arithmetic.multiplication.inverse
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.series.cauchy-product
open import real.series.geometric
open import real.subspace
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import sequence.partial-sums
open import subset.subspace

polylog-neg1-terms : ℝ -> ℕ -> ℝ
polylog-neg1-terms x n = ℕ->Semiring n * x ^ℕ n

private
  1/1-x : ∣ℝ∣< 1# -> ℝ
  1/1-x (x , ax<1) = ℝ1/ (diff x 1# , inj-r (diff-0<⁺ (trans-≤-< abs-≤ ax<1)))

polylog-neg1 : (∣ℝ∣< 1#) -> ℝ
polylog-neg1 x∈@(x , _) =
  x * (1/1-x x∈ * 1/1-x x∈)

opaque
  unfolding geometric-series-limit

  isLimit-polylog-neg1 : (x∈@(x , _) : ∣ℝ∣< 1#) ->
    isLimit (partial-sums (polylog-neg1-terms x)) (polylog-neg1 x∈)
  isLimit-polylog-neg1 x∈@(x , ax<1) = dropN-reflects-limit lim3
    where
    lim1 : isLimit (partial-sums (cauchy-product (geometric-sequence x) (geometric-sequence x)))
                   (geometric-series-limit x∈ * geometric-series-limit x∈)
    lim1 = isLimit-cauchy-product (isLimit-geometric-series x∈) (isLimit-geometric-series x∈)
                                  (isAbsConvergentSeries-geometric-sequence x∈)

    lim2 : isLimit (partial-sums (\n ->
                      x * (cauchy-product (geometric-sequence x) (geometric-sequence x) n)))
                   (polylog-neg1 x∈)
    lim2 = subst2 isLimit (funExt (\_ -> sym finiteSum-*)) refl
             (*₁-preserves-limit lim1)

    p1 : ∀ n -> (x * (cauchy-product (geometric-sequence x) (geometric-sequence x) n)) ==
                ℕ->Semiring (suc n) * x ^ℕ (suc n)
    p1 n =
      *-right (cong finiteSum (funExt (\((fin-pair+ i j i+j=n) : FinPair+ n) ->
                 sym (^ℕ-distrib-+-left i j) >=> cong (x ^ℕ_) i+j=n)) >=>
               finiteSum-constant) >=>
      sym *-assoc >=> *-left *-commute >=> *-assoc

    p2 : ∀ n -> partial-sums (\i -> ℕ->Semiring i * x ^ℕ i) (suc n) ==
                partial-sums (\i -> ℕ->Semiring (suc i) * x ^ℕ (suc i)) n
    p2 n = partial-sums-suc >=>
           +-left (*-left ℕ->Semiring-preserves-0# >=>
                   *-left-zero) >=>
           +-left-zero

    lim3 : isLimit (partial-sums (polylog-neg1-terms x) ∘ suc) (polylog-neg1 x∈)
    lim3 = subst2 isLimit
             (funExt (\n -> cong finiteSum (funExt (\(i , _) -> p1 i)) >=>
                            sym (p2 n)))
             refl lim2
