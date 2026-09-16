{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.taylor-series-integers where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import nat.even-odd
open import additive-group.instances.real
open import base
open import fin
open import combinatorics.factorial
open import equality
open import functions
open import heyting-field.instances.real
open import int.add1
open import int.addition
open import int.base
open import int.multiplication
open import modular-integers
open import nat
open import fin.sum-pair
open import nat.iteration
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.exponential-series
open import real.series
open import real.trigonometry.functions
open import real.trigonometry.taylor-series
open import real.trigonometry.identities.pythagorean
open import real.trigonometry.identities.parity
open import ring
open import isomorphism
open import ring.implementations.int
open import ring.implementations.real
open import semiring
open import semiring.initial
open import semiring.exponentiation
open import semiring.natural-reciprocal
open import set-quotient
open import truncation
open import combinatorics.binomial-coefficients
open import combinatorics.properties.binomial-coefficients-factorial

--          0
-- 0 1 0 -1 0 1 0 -1

-- alt-coeff : ℝ -> ℝ -> ℕ -> ℝ
-- alt-coeff a b zero    = a
-- alt-coeff a b (suc n) = alt-coeff b (- a) n

alt-coeff⁻ : ℝ -> ℝ -> ℕ -> ℝ
alt-coeff⁻ a b zero    = a
alt-coeff⁻ a b (suc n) = alt-coeff⁻ (- b) a n



alt-coeff/ℤ : ℝ -> ℝ -> ℤ -> ℝ
alt-coeff/ℤ a b (nonneg i) = alt-coeff a b i
alt-coeff/ℤ a b (neg i) = alt-coeff⁻ a b (suc i)


alt-coeff/ℤ-add1 : ∀ a b i -> alt-coeff/ℤ a b (add1 i) == alt-coeff/ℤ b (- a) i
alt-coeff/ℤ-add1 a b (nonneg i) = refl
alt-coeff/ℤ-add1 a b (neg zero) = sym minus-double-inverse
alt-coeff/ℤ-add1 a b (neg (suc i)) = \ii -> alt-coeff/ℤ (a-path ii) b (neg i)
  where
  a-path : a == (- (- a))
  a-path = sym minus-double-inverse


private
  add4 : ℤ -> ℤ
  add4 = add1 ∘ add1 ∘ add1 ∘ add1


alt-coeff/ℤ-add4 : ∀ a b i -> alt-coeff/ℤ a b (add4 i) == alt-coeff/ℤ a b i
alt-coeff/ℤ-add4 a b i =
  alt-coeff/ℤ-add1 a b (add1 (add1 (add1 i))) >=>
  alt-coeff/ℤ-add1 b (- a) (add1 (add1 i)) >=>
  alt-coeff/ℤ-add1 (- a) (- b) (add1 i) >=>
  alt-coeff/ℤ-add1 (- b) (- (- a)) i >=>
  cong2 (\a b -> alt-coeff/ℤ a b i) minus-double-inverse minus-double-inverse


opaque
  ℤ/nℤ-rec : {ℓ : Level} {n : ℕ}
    {P : ∀ (i₁ i₂ : ℤ) -> Type ℓ}
    (r : ∀ i -> P i i)
    (d : ∀ i j -> P i j <-> P i (int n + j)) ->
    ∀ i j -> ℤ/nℤ~ n i j -> P i j
  ℤ/nℤ-rec {ℓ} {n} {P} r d i j = ans-~
    where
    P' : ℤ -> ℤ -> Type ℓ
    P' j i = P i j

    d⁺ : ∀ i j -> P i j -> P i (int n + j)
    d⁺ i j = proj₁ (d i j)
    d⁻ : ∀ i j -> P i (int n + j) -> P i j
    d⁻ i j = proj₂ (d i j)

    d⁺ⁿ : ∀ i k -> P i (iter k (int n +_) i)
    d⁺ⁿ i zero = r i
    d⁺ⁿ i (suc k) = d⁺ i _ (d⁺ⁿ i k)

    d⁻ⁿ : ∀ j k -> P (iter k (int n +_) j) j
    d⁻ⁿ j zero = r j
    d⁻ⁿ j (suc k) =
      subst (P' j) (\ii -> iter-commute₁ k {f = int n +_} {g = int n +_} refl ii j)
        (d⁻ _ _ rec)
      where
      rec : P (iter k (int n +_) (int n + j)) (int n + j)
      rec = d⁻ⁿ (int n + j) k

    iter+ : ∀ k j -> iter k (int n +_) j == int k * int n + j
    iter+ zero j = sym (+-left *-left-zero >=> +-left-zero)
    iter+ (suc k) j =
      +-right (iter+ k j) >=>
      sym +-assoc >=>
      +-left (sym add1-extract-*)

    ans₁ : (k : ℕ) -> P i (int k * int n + i)
    ans₁ k = subst (P i) (iter+ k i) (d⁺ⁿ i k)

    ans₂ : (k : ℕ) -> P (int k * int n + j) j
    ans₂ k = subst (P' j) (iter+ k j) (d⁻ⁿ j k)


    ans-~ : ℤ/nℤ~ n i j -> P i j
    ans-~ (nonneg k , p) = subst (P i) (+-commute >=> +-right p >=> diff-step) (ans₁ k)
    ans-~ (neg k , p) = subst (P' j)
              (+-commute >=>
               +-right (minus-extract-left >=>
                        cong -_ p >=>
                        sym diff-anticommute) >=>
               diff-step)
              (ans₂ (suc k))



opaque
  unfolding _ℤ+_

  alt-coeff/ℤ/4ℤ : ℝ -> ℝ -> (ℤ/nℤ 4) -> ℝ
  alt-coeff/ℤ/4ℤ a b = SetQuotientElim.elim (\_ -> isSet-ℝ) (alt-coeff/ℤ a b) path
    where
    path : (i₁ i₂ : ℤ) -> ℤ/nℤ~ 4 i₁ i₂ -> alt-coeff/ℤ a b i₁ == alt-coeff/ℤ a b i₂
    path = ℤ/nℤ-rec (\_ -> refl) bij
      where
      bij : (i₁ i₂ : ℤ) -> (alt-coeff/ℤ a b i₁ == alt-coeff/ℤ a b i₂) <->
                           (alt-coeff/ℤ a b i₁ == alt-coeff/ℤ a b (int 4 + i₂))
      bij i₁ i₂ = (\p -> p >=> sym (alt-coeff/ℤ-add4 a b i₂)) ,
                  (\p -> p >=> (alt-coeff/ℤ-add4 a b i₂))
