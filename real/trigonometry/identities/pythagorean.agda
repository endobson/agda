{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.identities.pythagorean where


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


private
  -1^ℕ-Even : (n : ℕ) -> Even n -> Path ℝ ((- 1#) ^ℕ n) 1#
  -1^ℕ-Even n e = isEvenFunction-^ℕ n e 1# >=> ^ℕ-preserves-1# n
  -1^ℕ-Odd : (n : ℕ) -> Odd n -> Path ℝ ((- 1#) ^ℕ n) (- 1#)
  -1^ℕ-Odd n o = isOddFunction-^ℕ n o 1# >=> cong -_ (^ℕ-preserves-1# n)


module _ where -- TODO move somewhere else
  FinPairOdd->OddEven : {k : ℕ} -> ((fin-pair+ i j _) : FinPair+ k) ->
    Odd k -> (Odd i × Even j) ⊎ (Even i × Odd j)
  FinPairOdd->OddEven (fin-pair+ i j p) ok =
    Iso.fun (sum-Odd-iso i j) (subst Odd (sym p) ok)
  FinPairEven->OddEven : {k : ℕ} -> ((fin-pair+ i j _) : FinPair+ k) ->
    Even k -> (Even i × Even j) ⊎ (Odd i × Odd j)
  FinPairEven->OddEven (fin-pair+ i j p) ok =
    Iso.fun (sum-Even-iso i j) (subst Even (sym p) ok)


private
  sin-coeff-2n+1 : ∀ (n : ℕ) ->
    sin-coeff (suc (2 * n)) == (- 1#) ^ℕ n * 1/ℕ (factorial⁺ (suc (2 * n)))
  sin-coeff-2n+1 n = *-left (coeff-path n)
    where
    coeff-path : ∀ (n : ℕ) -> sin-alt-coeff (suc (2 * n)) == (- 1#) ^ℕ n
    coeff-path zero = refl
    coeff-path (suc zero) = sym *-right-one
    coeff-path (suc (suc n)) =
      cong sin-alt-coeff np >=>
      cong2 (\x y -> alt-coeff x y (suc (2 * n))) minus-double-inverse minus-double-inverse >=>
      coeff-path n >=>
      sym *-left-one >=>
      *-left (sym *-right-one >=> sym minus-extract-both) >=>
      *-assoc
      where
      np : suc (2 * (suc (suc n))) == suc (suc (suc (suc (suc (2 * n)))))
      np = cong (suc ∘ suc ∘ suc) (+-commuteᵉ n _ >=> cong (suc ∘ suc) (+-commuteᵉ _ n))


module _ where
  Even->half : (n : ℕ) -> Even n -> ℕ
  Even->half n e = fst (Even->div' {n} e)
  Odd->half⁻ : (n : ℕ) -> Odd n -> ℕ
  Odd->half⁻ (suc n) e = fst (Even->div' {n} e)
  Odd->half⁺ : (n : ℕ) -> Odd n -> ℕ
  Odd->half⁺ n e = fst (Even->div' {suc n} e)

  Odd->half-path : (n : ℕ) -> (o : Odd n) -> suc (Odd->half⁻ n o) == (Odd->half⁺ n o)
  Odd->half-path (suc n) o = refl

  -- Even->half-2n : (n : ℕ) -> (e : Even (2 * n)) -> Even->half (2 * n) e == n
  -- Even->half-2n

  sin-alt-coeff-Odd : ∀ (n : ℕ) -> (o : Odd n) -> sin-alt-coeff n == (- 1#) ^ℕ (Odd->half⁻ n o)
  sin-alt-coeff-Odd (suc zero) _ = refl
  sin-alt-coeff-Odd (suc (suc (suc zero))) _ = sym *-right-one
  sin-alt-coeff-Odd (suc (suc (suc (suc (suc n))))) o =
    cong2 (\x y -> alt-coeff x y (suc n)) minus-double-inverse minus-double-inverse >=>
    sin-alt-coeff-Odd (suc n) o >=>
    sym *-left-one >=>
    *-left (sym *-right-one >=> sym minus-extract-both) >=>
    *-assoc

  sin-coeff-Odd : ∀ (n : ℕ) -> (o : Odd n) ->
    sin-coeff n == (- 1#) ^ℕ (Odd->half⁻ n o) * 1/ℕ (factorial⁺ n)
  sin-coeff-Odd n o = *-left (sin-alt-coeff-Odd n o)

  cos-alt-coeff-Even : ∀ (n : ℕ) -> (e : Even n) -> cos-alt-coeff n == (- 1#) ^ℕ (Even->half n e)
  cos-alt-coeff-Even zero _ = refl
  cos-alt-coeff-Even (suc (suc zero)) _ = sym *-right-one
  cos-alt-coeff-Even (suc (suc (suc (suc n)))) e =
    cong2 (\x y -> alt-coeff x y n) minus-double-inverse minus-double-inverse >=>
    cos-alt-coeff-Even n e >=>
    sym *-left-one >=>
    *-left (sym *-right-one >=> sym minus-extract-both) >=>
    *-assoc

  cos-coeff-Even : ∀ (n : ℕ) -> (e : Even n) ->
    cos-coeff n == (- 1#) ^ℕ (Even->half n e) * 1/ℕ (factorial⁺ n)
  cos-coeff-Even n o = *-left (cos-alt-coeff-Even n o)

module _ where

  Even->half-distrib-+ :
    ∀ i j (eij : Even (i + j)) (ei : Even i) (ej : Even j) ->
      Even->half (i + j) eij == Even->half i ei + Even->half j ej
  Even->half-distrib-+ i j eij ei ej = *'-left-injective 2⁺ p
    where
    hi hj hij : ℕ
    hi = Even->half i ei
    hj = Even->half j ej
    hij = Even->half (i + j) eij

    p : 2 * hij == 2 * (hi + hj)
    p = *-commuteᵉ 2 hij >=>
        snd (Even->div' {i + j} eij) >=>
        cong2 _+_ (sym (snd (Even->div' {i} ei))) (sym (snd (Even->div' {j} ej))) >=>
        sym (*-distrib-+-rightᵉ hi hj 2) >=>
        *-commuteᵉ (hi + hj) 2

  Even->half-distrib-+' :
    ∀ i j (eij : Even (i + j)) (oi : Odd i) (oj : Odd j) ->
      Even->half (i + j) eij == Odd->half⁺ i oi + Odd->half⁻ j oj
  Even->half-distrib-+' i j@(suc j') eij oi oj = step₁ >=> step₂
    where
    ijp : i + j == suc i + j'
    ijp = +'-right-suc

    eij' : Even (suc i + j')
    eij' = transport (\k -> Even (ijp k)) eij

    eijp : PathP (\k -> Even (ijp k)) eij eij'
    eijp = transport-filler (\k -> Even (ijp k)) eij

    step₁ : Even->half (i + j) eij == Even->half (suc i + j') eij'
    step₁ k = Even->half (ijp k) (eijp k)

    step₂ : Even->half (suc i + j') eij' == Odd->half⁺ i oi + Odd->half⁻ j oj
    step₂ = Even->half-distrib-+ (suc i) j' eij' oi oj

module _ where
  fact-binomial-path : ∀ i j ->
    1/ℕ (factorial⁺ i) * 1/ℕ (factorial⁺ j) ==
    ℕ->Semiring (binomial-coeff' i j) * 1/ℕ (factorial⁺ (i + j))
  fact-binomial-path i j =
    sym *-right-one >=>
    *-right (sym (ℕ-1/ℕ-path (factorial⁺ (i + j)))) >=>
    sym *-assoc >=>
    *-left (cong2 _*_ (sym (1/ℕ-distrib-* _ _))
                      (cong ℕ->Semiring (sym (binomial-coeff'-factorial-path i j)) >=>
                       Semiringʰ.preserves-* ℕ->Semiringʰ (binomial-coeff' i j) _) >=>
            *-commute >=>
            *-assoc >=>
            *-right (ℕ-1/ℕ-path _) >=>
            *-right-one)

private
  sc-terms-path-even :
    ∀ x i j -> Even i -> Even j -> (e : Even (i + j)) ->
      sin-terms x i * sin-terms x j + cos-terms x i * cos-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      ((- 1#) ^ℕ (Even->half (i + j) e) * (1/ℕ (factorial⁺ (i + j)) * (x ^ℕ (i + j))))
  sc-terms-path-even x i j ei ej eij = cong2 _+_ step₁ step₂ >=> +-left-zero
    where
    hi hj hij : ℕ
    hi = Even->half i ei
    hj = Even->half j ej
    hij = Even->half (i + j) eij
    hij-path : hij == hi + hj
    hij-path = Even->half-distrib-+ i j eij ei ej


    step₁ : sin-terms x i * sin-terms x j == 0#
    step₁ = *-left (*-left (sin-coeff-Even i ei) >=> *-left-zero) >=> *-left-zero

    step₃ : (- 1#) ^ℕ i * 1# ^ℕ j == 1#
    step₃ = cong2 _*_ (-1^ℕ-Even i ei) (^ℕ-preserves-1# j) >=>
            *-right-one


    step₂ : cos-terms x i * cos-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      (((- 1#) ^ℕ hij) * (1/ℕ (factorial⁺ (i + j)) * (x ^ℕ (i + j))))

    step₂ =
      *-swap >=>
      *-left (cong2 _*_ (cos-coeff-Even i ei) (cos-coeff-Even j ej) >=>
              *-swap >=>
              *-right (fact-binomial-path i j) >=>
              sym *-assoc) >=>
      *-assoc >=>
      *-left (*-commute >=> *-right (sym (^ℕ-distrib-+-left hi hj) >=> cong ((- 1#) ^ℕ_) (sym hij-path))) >=>
      *-right (*-right (sym (^ℕ-distrib-+-left i j))) >=>
      *-assoc >=>
      *-left (sym *-right-one >=> *-right (sym step₃))

  sc-terms-path-odd :
    ∀ x i j -> Odd i -> Odd j -> (e : Even (i + j)) ->
      sin-terms x i * sin-terms x j + cos-terms x i * cos-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      (((- 1#) ^ℕ (Even->half (i + j) e)) * (1/ℕ (factorial⁺ (i + j)) * (x ^ℕ (i + j))))
  sc-terms-path-odd x i@(suc i') j@(suc j') oi oj eij =
    cong2 _+_ step₂ step₁ >=> +-right-zero
    where
    hi⁺ hi⁻ hj⁻ hij : ℕ
    hi⁺ = Odd->half⁺ i oi
    hi⁻ = Odd->half⁻ i oi
    hj⁻ = Odd->half⁻ j oj
    hij = Even->half (i + j) eij
    hij-path : hij == hi⁺ + hj⁻
    hij-path = Even->half-distrib-+' i j eij oi oj
    check-hi : hi⁺ == suc hi⁻
    check-hi = refl


    step₁ : cos-terms x i * cos-terms x j == 0#
    step₁ = *-left (*-left (cos-coeff-Odd i oi) >=> *-left-zero) >=> *-left-zero

    step₃ : ((- 1#) ^ℕ (hi⁻ + hj⁻)) == (- 1#) * ((- 1#) ^ℕ hij)
    step₃ =
      sym *-left-one >=>
      *-left (sym *-left-one >=> sym minus-extract-both) >=>
      *-assoc >=>
      (\k -> (- 1#) * ((- 1#) ^ℕ hij-path (~ k)))

    step₄ : (- 1#) ^ℕ i * 1# ^ℕ j == - 1#
    step₄ = cong2 _*_ (-1^ℕ-Odd i oi) (^ℕ-preserves-1# j) >=>
            *-right-one


    step₂ : sin-terms x i * sin-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      (((- 1#) ^ℕ hij) * (1/ℕ (factorial⁺ (i + j)) * (x ^ℕ (i + j))))
    step₂ =
      *-swap >=>
      *-left (cong2 _*_ (sin-coeff-Odd i oi) (sin-coeff-Odd j oj) >=>
              *-swap >=>
              *-right (fact-binomial-path i j) >=>
              sym *-assoc) >=>
      *-assoc >=>
      *-left (*-commute >=>
              *-right (sym (^ℕ-distrib-+-left hi⁻ hj⁻) >=> step₃) >=>
              sym *-assoc >=>
              *-left (*-right (sym step₄))) >=>
      *-right (*-right (sym (^ℕ-distrib-+-left i j))) >=>
      *-assoc

  sc-terms-path₁ :
    ∀ x i j -> (e : Even (i + j)) ->
      sin-terms x i * sin-terms x j + cos-terms x i * cos-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      ((- 1#) ^ℕ (Even->half (i + j) e) * (1/ℕ (factorial⁺ (i + j)) * (x ^ℕ (i + j))))
  sc-terms-path₁ x i j e =
    case (FinPairEven->OddEven (fin-pair+ i j refl) e) of
      (\{ (inj-l (ei , ej)) -> sc-terms-path-even x i j ei ej e
        ; (inj-r (oi , oj)) -> sc-terms-path-odd x i j oi oj e
        })


  sc-terms-path₂ :
    ∀ x k (e : Even k) -> ((fin-pair+ i j _) : FinPair+ k) ->
      sin-terms x i * sin-terms x j + cos-terms x i * cos-terms x j ==
      (ℕ->Semiring (binomial-coeff' i j) * ((- 1#) ^ℕ i * 1# ^ℕ j)) *
      ((- 1#) ^ℕ (Even->half k e) * (1/ℕ (factorial⁺ k) * (x ^ℕ k)))
  sc-terms-path₂ x k e (fin-pair+ i j p) =
    sc-terms-path₁ x i j e' >=>
    *-right (\ii -> ((- 1#) ^ℕ (Even->half (p ii) (ep (~ ii)))) *
                    (1/ℕ (factorial⁺ (p ii)) * (x ^ℕ (p ii))))
    where
    e' : Even (i + j)
    e' = transport (\k -> Even (p (~ k))) e

    ep : PathP (\k -> Even (p (~ k))) e e'
    ep = transport-filler (\k -> Even (p (~ k))) e


opaque
  pythagorean-identity : ∀ (x : ℝ) -> (sin x) * (sin x) + (cos x) * (cos x) == 1#
  pythagorean-identity x =
    cong fst (isProp-isConvergentSequence (_ , isLimit-st²ct²') (_ , isLimit-1))
    where

    st : ℕ -> ℝ
    st = sin-terms x
    ct : ℕ -> ℝ
    ct = cos-terms x

    ac-sin : isAbsConvergentSeries st
    ac-sin = isAbsConvergentSeries-sin x
    ac-cos : isAbsConvergentSeries ct
    ac-cos = isAbsConvergentSeries-cos x

    isLimit-st : isLimit (partial-sums st) (sin x)
    isLimit-st = snd (isAbsConvergentSeries->isConvergentSeries ac-sin)
    isLimit-ct : isLimit (partial-sums ct) (cos x)
    isLimit-ct = snd (isAbsConvergentSeries->isConvergentSeries ac-cos)

    isLimit-st² : isLimit (partial-sums (cauchy-product st st)) (sin x * sin x)
    isLimit-st² = isLimit-cauchy-product isLimit-st isLimit-st ac-sin
    isLimit-ct² : isLimit (partial-sums (cauchy-product ct ct)) (cos x * cos x)
    isLimit-ct² = isLimit-cauchy-product isLimit-ct isLimit-ct ac-cos

    isLimit-st²ct² : isLimit (\i -> partial-sums (cauchy-product st st) i +
                                    partial-sums (cauchy-product ct ct) i)
                             (sin x * sin x + cos x * cos x)
    isLimit-st²ct² = +-preserves-limit isLimit-st² isLimit-ct²

    step₁ : ∀ i ->
       partial-sums (cauchy-product st st) i + partial-sums (cauchy-product ct ct) i ==
       partial-sums (\j -> cauchy-product st st j + cauchy-product ct ct j) i
    step₁ i = sym finiteSum-+

    step₂ : cauchy-product st st 0 + cauchy-product ct ct 0 == 1#
    step₂ =
      cong2 _+_ (finiteMerge-isContr isContr-FinPair+-0)
                (finiteMerge-isContr isContr-FinPair+-0) >=>
      reflᵉ ((((0# * 1/ℕ 1⁺) * (x ^ℕ 0#)) * ((0# * 1/ℕ 1⁺) * (x ^ℕ 0#))) +
             (((1# * 1/ℕ 1⁺) * (x ^ℕ 0#)) * ((1# * 1/ℕ 1⁺) * (x ^ℕ 0#)))) >=>
      (\i -> inner 0# i * inner 0# i + inner 1# i * inner 1# i) >=>
      cong2 _+_ *-right-zero *-right-one >=>
      +-left-zero
      where
      inner : (z : ℝ) -> (z * 1/ℕ 1⁺) * (x ^ℕ 0#) == z
      inner _ = *-right-one >=> *-right 1/1-path >=> *-right-one


    step₃ : ∀ k -> cauchy-product st st (suc k) + cauchy-product ct ct (suc k) == 0#
    step₃ k = case (fst (isContr-OddEven k)) of either odd-case even-case
      where
      even-case : (ek : Even k) -> cauchy-product st st (suc k) + cauchy-product ct ct (suc k) == 0#
      even-case ek = cong2 _+_ st-zero ct-zero >=> +-right-zero
        where
        st-zero : cauchy-product st st (suc k) == 0#
        st-zero = finiteMerge-ε (\ fp@(fin-pair+ i j p) -> case (FinPairOdd->OddEven fp ek) of
          (\{ (inj-l (oi , ej)) ->
              *-right (*-left (sin-coeff-Even j ej) >=> *-left-zero) >=> *-right-zero
            ; (inj-r (ei , oj)) ->
              *-left (*-left (sin-coeff-Even i ei) >=> *-left-zero) >=> *-left-zero
            }))

        ct-zero : cauchy-product ct ct (suc k) == 0#
        ct-zero = finiteMerge-ε (\ fp@(fin-pair+ i j p) -> case (FinPairOdd->OddEven fp ek) of
          (\{ (inj-l (oi , ej)) ->
              *-left (*-left (cos-coeff-Odd i oi) >=> *-left-zero) >=> *-left-zero
            ; (inj-r (ei , oj)) ->
              *-right (*-left (cos-coeff-Odd j oj) >=> *-left-zero) >=> *-right-zero
            }))

      odd-case : (ok : Odd k) -> cauchy-product st st (suc k) + cauchy-product ct ct (suc k) == 0#
      odd-case ok =
        sym finiteSum-+ >=>
        cong finiteSum (funExt (\ fp -> sc-terms-path₂ x (suc k) ok fp >=> *-commute)) >=>
        finiteSum-* >=>
        *-right (sym (binomial-expansion-path (- 1#) 1# (suc k)) >=>
                 cong (_^ℕ (suc k)) (+-commute >=> +-inverse) >=>
                 *-left-zero) >=>
        *-right-zero

    step₄ : ∀ (i : Nat) ->
       partial-sums (\j -> cauchy-product st st j + cauchy-product ct ct j) (suc i) ==
       1#
    step₄ i =
      sym (partial-sums-dropN (\j -> cauchy-product st st j + cauchy-product ct ct j) 1 i) >=>
      +-left (finiteMerge-Fin1 >=> step₂) >=>
      +-right (finiteMerge-ε (\ ((j , _) : Fin i) -> step₃ j)) >=>
      +-right-zero


    isLimit-st²ct²' : isLimit (\i -> 1#)
                              (sin x * sin x + cos x * cos x)
    isLimit-st²ct²' =
      subst (\s -> isLimit s (sin x * sin x + cos x * cos x))
        (funExt (\i -> step₁ (suc i) >=> step₄ i))
        (dropN-preserves-limit isLimit-st²ct²)


    isLimit-1 : isLimit (\i -> 1#) 1#

    isLimit-1 = isLimit-constant-seq 1#
