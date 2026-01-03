{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.continuous where

open import additive-group
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import equality
open import funext
open import heyting-field.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import nat.order
open import order
open import order.bound
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import real
open import real.continuous.arithmetic.multiplication
open import real.exponential-series
open import real.exponential.plus
open import real.sequence.limit
open import real.power-series.bounded
open import real.subspace
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import subset.subspace
open import truncation


private
  ub-exp-coeff : isUpperBound (\n -> (abs (1/ℕ (factorial⁺ n)))) 1#
  ub-exp-coeff n =
    trans-≤-= (trans-=-≤ (abs-0≤-path (weaken-< (0<1/ℕ _)))
                         (1/ℕ-flips-≤ _ _ (Pos'->< (snd (factorial⁺ n))))) 1/1-path

  exp' : ∣ℝ∣< 1# -> ℝ
  exp' = eval-Bounded-power-series ub-exp-coeff

  isContinuous-exp' : isContinuous exp'
  isContinuous-exp' = isContinuous-eval-Bounded-power-series ub-exp-coeff

  exp'-path : (x∈@(x , _) : ∣ℝ∣< 1#) -> exp' x∈ == exp x
  exp'-path x∈@(x , _) =
    cong fst (isProp-isConvergentSequence (_ , isLimit-eval-Bounded-power-series ub-exp-coeff x∈)
                                          (_ , isLimit-exp x))

  0' : ∣ℝ∣< 1#
  0' = 0# , trans-=-< (abs-0≤-path refl-≤) 0<1

  isContinuousAt-exp-0 : isContinuousAt exp 0#
  isContinuousAt-exp-0 ε⁺ = ∥-map handle (isContinuous.at isContinuous-exp' 0' ε⁺)
    where
    handle : Σ[ δ ∈ ℝ⁺ ] (∀ y∈ -> εClose δ 0' y∈ -> εClose ε⁺ (exp' 0') (exp' y∈)) ->
             Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ 0# y -> εClose ε⁺ (exp 0#) (exp y))
    handle ((δ , 0<δ) , close') = (δ2 , 0<δ2) , close
      where
      δ2 : ℝ
      δ2 = min δ 1#
      0<δ2 : 0# < δ2
      0<δ2 = min-greatest-< 0<δ 0<1
      close : ∀ y -> εClose (δ2 , 0<δ2) 0# y -> εClose ε⁺ (exp 0#) (exp y)
      close y d0y<δ2 =
        subst2 (εClose ε⁺) (exp'-path 0') (exp'-path y∈) (close' y∈ (trans-<-≤ d0y<δ2 min-≤-left))
        where
        y∈ : ∣ℝ∣< 1#
        y∈ = y , trans-=-< (cong abs (sym diff0-path)) (trans-<-≤ d0y<δ2 min-≤-right)

  isContinuousAt-exp1 : (c : ℝ) -> isContinuousAt (\x -> exp x * exp c) 0#
  isContinuousAt-exp1 c = isContinuousAt-*₂ isContinuousAt-exp-0
  isContinuousAt-exp2 : (c : ℝ) -> isContinuousAt (\x -> exp (x + c)) 0#
  isContinuousAt-exp2 c =
    subst2 isContinuousAt (funExt (\x -> sym (exp-+-path x c))) refl (isContinuousAt-exp1 c)

  isContinuousAt-exp3 : (c : ℝ) -> isContinuousAt exp c
  isContinuousAt-exp3 c ε⁺ = ∥-map handle (isContinuousAt-exp2 c ε⁺)
    where
    handle : Σ[ δ ∈ ℝ⁺ ] (∀ x -> εClose δ 0# x -> εClose ε⁺ (exp (0# + c)) (exp (x + c))) ->
             Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ c y -> εClose ε⁺ (exp c) (exp y))
    handle (δ⁺ , close) = δ⁺ , close'
      where
      close' : ∀ y -> εClose δ⁺ c y -> εClose ε⁺ (exp c) (exp y)
      close' y dcy<ε = trans-=-< (cong2 distance p1 p2) (close (diff c y) lt)
        where
        p1 : exp c == exp (0# + c)
        p1 = cong exp (sym +-left-zero)
        p2 : exp y == exp (diff c y + c)
        p2 = cong exp (sym diff-step >=> +-commute)
        lt : distance 0# (diff c y) < _
        lt = trans-=-< (cong abs diff0-path) dcy<ε

opaque
  isContinuous-exp : isContinuous exp
  isContinuous-exp .isContinuous.at x = isContinuousAt-exp3 x
