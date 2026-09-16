{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.identities.parity where

open import additive-group
open import additive-group.functions
open import additive-group.instances.real
open import base
open import equality-path
open import fin
open import finset.instances
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import nat
open import nat.even-odd
open import real
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.series
open import real.trigonometry.functions
open import real.trigonometry.taylor-series
open import ring
open import ring.exponentiation
open import ring.implementations.real
open import semiring
open import sequence.partial-sums
open import sum


private
  alt-coeff-Even : ∀ (b : ℝ) -> (n : ℕ) -> Even n -> alt-coeff 0# b n == 0#
  alt-coeff-Odd : ∀ (a : ℝ) -> (n : ℕ) -> Odd n -> alt-coeff a 0# n == 0#
  alt-coeff-Even b zero tt = refl
  alt-coeff-Even b (suc n) o =
    cong (\x -> alt-coeff b x n) minus-zero >=> alt-coeff-Odd b n o
  alt-coeff-Odd a zero ()
  alt-coeff-Odd a (suc n) e = alt-coeff-Even (- a) n e

opaque
  sin-alt-coeff-Even : ∀ (n : ℕ) -> Even n -> sin-alt-coeff n == 0#
  sin-alt-coeff-Even n e = (alt-coeff-Even 1# n e)
  cos-alt-coeff-Odd : ∀ (n : ℕ) -> Odd n -> cos-alt-coeff n == 0#
  cos-alt-coeff-Odd n o = (alt-coeff-Odd 1# n o)

  sin-coeff-Even : ∀ (n : ℕ) -> Even n -> sin-coeff n == 0#
  sin-coeff-Even n e = *-left (sin-alt-coeff-Even n e) >=> *-left-zero
  cos-coeff-Odd : ∀ (n : ℕ) -> Odd n -> cos-coeff n == 0#
  cos-coeff-Odd n o = *-left (cos-alt-coeff-Odd n o) >=> *-left-zero

opaque
  isEvenFunction-cos : isEvenFunction cos
  isEvenFunction-cos x =
    cong fst (isProp-isConvergentSequence (_ , l₁) (_ , l₂))
    where

    cos-terms-even-path : ∀ n -> Even n -> cos-terms (- x) n == cos-terms x n
    cos-terms-even-path n e =
      *-right (isEvenFunction-^ℕ n e x)

    cos-terms-odd-path : ∀ n -> Odd n -> cos-terms (- x) n == cos-terms x n
    cos-terms-odd-path n o =
      *-left (cos-coeff-Odd n o) >=>
      *-left-zero >=>
      sym *-left-zero >=>
      *-left (sym (cos-coeff-Odd n o))

    cos-terms-path : ∀ n -> cos-terms (- x) n == cos-terms x n
    cos-terms-path n =
      either (cos-terms-odd-path n) (cos-terms-even-path n) (fst (isContr-OddEven n))

    l₁ : isLimit (partial-sums (cos-terms x)) (cos (- x))
    l₁ = transport (\i -> isLimit (partial-sums (funExt cos-terms-path i)) (cos (- x)))
                   (isLimit-cos-terms (- x))

    l₂ : isLimit (partial-sums (cos-terms x)) (cos x)
    l₂ = isLimit-cos-terms x


opaque
  isOddFunction-sin : isOddFunction sin
  isOddFunction-sin x =
    cong fst (isProp-isConvergentSequence (_ , l₁) (_ , l₂))
    where

    sin-terms-even-path : ∀ n -> Even n -> sin-terms (- x) n == - (sin-terms x n)
    sin-terms-even-path n e =
      *-left (sin-coeff-Even n e) >=>
      *-left-zero >=>
      sym minus-zero >=>
      cong -_ (sym *-left-zero >=>
               *-left (sym (sin-coeff-Even n e)))

    sin-terms-odd-path : ∀ n -> Odd n -> sin-terms (- x) n == - (sin-terms x n)
    sin-terms-odd-path n o =
      *-right (isOddFunction-^ℕ n o x) >=>
      minus-extract-right

    sin-terms-path : ∀ n -> sin-terms (- x) n == - (sin-terms x n)
    sin-terms-path n =
      either (sin-terms-odd-path n) (sin-terms-even-path n) (fst (isContr-OddEven n))

    Σsin-terms-path : ∀ n -> (partial-sums (sin-terms (- x)) n) ==
                             - (partial-sums (sin-terms x) n)
    Σsin-terms-path n =
      cong finiteSum (funExt (\ (n , _) -> sin-terms-path n)) >=>
      finiteSum--

    l₁ : isLimit (-_ ∘ partial-sums (sin-terms x)) (sin (- x))
    l₁ = transport (\i -> isLimit (funExt Σsin-terms-path i) (sin (- x)))
                   (isLimit-sin-terms (- x))

    l₂ : isLimit (-_ ∘ partial-sums (sin-terms x)) (- (sin x))
    l₂ = minus-preserves-limit (isLimit-sin-terms x)
