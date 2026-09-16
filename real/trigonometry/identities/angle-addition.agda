{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.identities.angle-addition where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.triangle-numbers
open import cubical
open import combinatorics.factorial
open import combinatorics.binomial-coefficients
open import combinatorics.properties.binomial-coefficients-factorial
open import decision
open import equality-path
open import equivalence
open import equivalence.base
open import fin.sum-pair
open import finite-commutative-monoid.small
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import fin
open import functions
open import funext
open import hlevel.base
open import hlevel.sigma
open import isomorphism
open import nat
open import nat.even-odd
open import nat.iteration
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring.instances.real
open import real
open import real.infinite-sum
open import real.infinite-sum.triangle
open import real.infinite-sum.cauchy-triangle
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.order
open import real.sequence.limit.subsequence
open import real.series
open import real.series.base
open import real.series.cauchy-product
open import real.trigonometry.functions
open import real.trigonometry.identities.parity
open import real.trigonometry.taylor-series
open import relation
open import ring
open import ring.exponentiation
open import ring.implementations.real
open import semiring
open import semiring.exponentiation.binomial-expansion
open import semiring.initial
open import semiring.instances.nat
open import semiring.exponentiation
open import semiring.natural-reciprocal
open import sequence
open import sequence.partial-sums
open import sequence.subsequence
open import sigma
open import sum
open import sigma.base
open import truncation
open import finsum.arithmetic
open import real.trigonometry.identities.pythagorean
open import real.trigonometry.identities.parity



private
  module _ (x y : ℝ) where
    sc-terms-path₁ :
      ∀ i j ->
        cos-terms x i * cos-terms y j + (- (sin-terms x i * sin-terms y j)) ==
        cos-coeff (i + j) * (ℕ->Semiring (binomial-coeff' i j) * ((x ^ℕ i) * (y ^ℕ j)))
    sc-terms-path₁ i j = p-cs
      where
      c-path :
        ((cos-alt-coeff i * cos-alt-coeff j) + (- (sin-alt-coeff i * sin-alt-coeff j))) ==
        cos-alt-coeff (i + j)
      c-path = handle (fst (isContr-OddEven i)) (fst (isContr-OddEven j))
        where
        c-OddEven : Odd i -> Even j ->
          ((cos-alt-coeff i * cos-alt-coeff j) + (- (sin-alt-coeff i * sin-alt-coeff j))) ==
          cos-alt-coeff (i + j)
        c-OddEven oi ej =
          cong2 diff (*-right (sin-alt-coeff-Even j ej) >=> *-right-zero)
                     (*-left (cos-alt-coeff-Odd i oi) >=> *-left-zero) >=>
          +-right minus-zero >=>
          +-right-zero >=>
          sym (cos-alt-coeff-Odd (i + j) oij)
          where
          oij : Odd (i + j)
          oij = Iso.inv (sum-Odd-iso i j) (inj-l (oi , ej))

        c-EvenOdd : Even i -> Odd j ->
          ((cos-alt-coeff i * cos-alt-coeff j) + (- (sin-alt-coeff i * sin-alt-coeff j))) ==
          cos-alt-coeff (i + j)
        c-EvenOdd ei oj =
          cong2 diff (*-left (sin-alt-coeff-Even i ei) >=> *-left-zero)
                     (*-right (cos-alt-coeff-Odd j oj) >=> *-right-zero) >=>
          +-right minus-zero >=>
          +-right-zero >=>
          sym (cos-alt-coeff-Odd (i + j) oij)
          where
          oij : Odd (i + j)
          oij = Iso.inv (sum-Odd-iso i j) (inj-r (ei , oj))


        c-OddOdd : Odd i -> Odd j ->
          ((cos-alt-coeff i * cos-alt-coeff j) + (- (sin-alt-coeff i * sin-alt-coeff j))) ==
          cos-alt-coeff (i + j)
        c-OddOdd oi oj =
          +-left (*-left (cos-alt-coeff-Odd i oi) >=> *-left-zero) >=>
          +-left-zero >=>
          cong -_ (*-cong (sin-alt-coeff-Odd i oi) (sin-alt-coeff-Odd j oj) >=>
                   sym (^ℕ-distrib-+-left i/2 j/2) >=>
                   sym *-left-one) >=>
          sym minus-extract-left >=>
          reflᵉ ((- 1#) ^ℕ (suc i/2 +' j/2)) >=>
          cong ((- 1#) ^ℕ_) (+-left (Odd->half-path i oi) >=>
                             (sym (Even->half-distrib-+' i j eij oi oj))) >=>
          sym (cos-alt-coeff-Even (i + j) eij)
          where
          i/2 j/2 : ℕ
          i/2 = Odd->half⁻ i oi
          j/2 = Odd->half⁻ j oj

          eij : Even (i + j)
          eij = Iso.inv (sum-Even-iso i j) (inj-r (oi , oj))


        c-EvenEven : Even i -> Even j ->
          ((cos-alt-coeff i * cos-alt-coeff j) + (- (sin-alt-coeff i * sin-alt-coeff j))) ==
          cos-alt-coeff (i + j)
        c-EvenEven ei ej =
          +-right (cong -_ (*-left (sin-alt-coeff-Even i ei) >=> *-left-zero) >=>
                   minus-zero) >=>
          +-right-zero >=>
          *-cong (cos-alt-coeff-Even i ei) (cos-alt-coeff-Even j ej) >=>
          sym (^ℕ-distrib-+-left i/2 j/2) >=>
          cong ((- 1#) ^ℕ_) (sym (Even->half-distrib-+ i j eij ei ej)) >=>
          sym (cos-alt-coeff-Even (i + j) eij)

          where
          i/2 j/2 : ℕ
          i/2 = Even->half i ei
          j/2 = Even->half j ej

          eij : Even (i + j)
          eij = Iso.inv (sum-Even-iso i j) (inj-l (ei , ej))


        handle : _ -> _ -> _
        handle (inj-l oi) (inj-l oj) = c-OddOdd oi oj
        handle (inj-l oi) (inj-r ej) = c-OddEven oi ej
        handle (inj-r ei) (inj-l oj) = c-EvenOdd ei oj
        handle (inj-r ei) (inj-r ej) = c-EvenEven ei ej



      p-cs :
        cos-terms x i * cos-terms y j + (- (sin-terms x i * sin-terms y j)) ==
        cos-coeff (i + j) * (ℕ->Semiring (binomial-coeff' i j) * ((x ^ℕ i) * (y ^ℕ j)))
      p-cs =
        cong2 diff p-sin p-cos >=>
        sym *-distrib-diff-right >=>
        *-left c-path >=>
        *-right *-assoc >=>
        sym *-assoc >=>
        sym *-swap
        where
        p-cos :
          cos-terms x i * cos-terms y j ==
          (cos-alt-coeff i * cos-alt-coeff j) *
          ((ℕ->Semiring (binomial-coeff' i j) * 1/ℕ (factorial⁺ (i + j))) *
           ((x ^ℕ i) * (y ^ℕ j)))
        p-cos = *-swap >=>
                *-left (*-swap >=> *-right (fact-binomial-path i j)) >=>
                *-assoc

        p-sin :
          sin-terms x i * sin-terms y j ==
          (sin-alt-coeff i * sin-alt-coeff j) *
          ((ℕ->Semiring (binomial-coeff' i j) * 1/ℕ (factorial⁺ (i + j))) *
           ((x ^ℕ i) * (y ^ℕ j)))
        p-sin = *-swap >=>
                *-left (*-swap >=> *-right (fact-binomial-path i j)) >=>
                *-assoc



opaque
  cos-+-path : ∀ (x y : ℝ) -> cos (x + y) == (cos x) * (cos y) + (- ((sin x) * (sin y)))
  cos-+-path x y =
    cong fst (isProp-isConvergentSequence (_ , l₆) (_ , l₅))
    where
    s₁ : Sequence ℝ
    s₁ = partial-sums (cos-terms (x + y))

    l₁ : isLimit s₁ (cos (x + y))
    l₁ = isLimit-cos-terms (x + y)


    r₂ : Sequence ℝ
    r₂ n =
      cos-coeff n *
      finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))

    s₁=s₂ : s₁ == (partial-sums r₂)
    s₁=s₂ = cong partial-sums (funExt (\n -> *-right (binomial-expansion-path x y n)))


    r₃ : Sequence ℝ
    r₃ = cauchy-product (cos-terms x) (cos-terms y)

    r₄ : Sequence ℝ
    r₄ = cauchy-product (sin-terms x) (sin-terms y)

    r₅ : Sequence ℝ
    r₅ n = diff (r₄ n) (r₃ n)

    l₅ : isLimit (partial-sums r₅) ((cos x * cos y) + (- (sin x * sin y)))
    l₅ = subst (\s -> isLimit s ((cos x * cos y) + (- (sin x * sin y))))
          (funExt r-path) l₃₄
      where
      l₃₄ : isLimit (\n -> partial-sums r₃ n + - (partial-sums r₄ n))
                    ((cos x * cos y) + (- (sin x * sin y)))
      l₃₄ =
        +-preserves-limit
          (isLimit-cauchy-product (isLimit-cos-terms x) (isLimit-cos-terms y)
            (isAbsConvergentSeries-cos x))
          (minus-preserves-limit
            (isLimit-cauchy-product (isLimit-sin-terms x) (isLimit-sin-terms y)
              (isAbsConvergentSeries-sin x)))

      r-path : ∀ n -> partial-sums r₃ n + - (partial-sums r₄ n) ==
                       partial-sums r₅ n
      r-path n =
        +-right (sym finiteSum--) >=>
        sym finiteSum-+

    r₂=r₅ : ∀ n -> r₂ n == r₅ n
    r₂=r₅ n =
      sym finiteSum-* >=>
      cong finiteSum (funExt (\ (fin-pair+ i j p) ->
                       *-left (cong cos-coeff (sym p)) >=>
                       (sym (sc-terms-path₁ x y i j)))) >=>
      finiteSum-diff

    l₆ : isLimit (partial-sums r₅) (cos (x + y))
    l₆ = subst (\s -> isLimit s (cos (x + y)))
           (s₁=s₂ >=> cong partial-sums (funExt r₂=r₅)) l₁
