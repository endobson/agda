{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.binomial-theorem where

open import semiring
open import semiring.instances.nat
open import semiring.exponentiation
open import base
open import nat
open import equality-path
open import finsum
open import commutative-monoid
open import fin.sum-pair
open import additive-group
open import additive-group.instances.nat
open import combinatorics.binomial-coefficients
open import semiring.initial
open import finset.instances.sum-pair
open import finset.instances
open import finsum.arithmetic
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import maybe
open import funext
open import equivalence
open import functions
open import isomorphism

{-
module _
  {ℓD : Level} {D : Type ℓD} {CM : CommMonoid D}
  where
  private
    module CM = CommMonoid CM

  finiteMerge-fin-pair+-rec₁ :
    ∀ {n : Nat} {d : D} {ds : FinPair+ n -> D} ->
      finiteMerge CM (fin-pair+-rec₁ d ds) ==
      d CM.∙ finiteMerge CM ds
  finiteMerge-fin-pair+-rec₁ {n} {d} {ds} =
    sym (step₁ >=> step₂ >=> cong (finiteMerge CM) step₃)
    where
    f : Maybe (FinPair+ n) -> FinPair+ (suc n)
    f = maybe fin-pair+-zero₁ fin-pair+-suc₁
    b : FinPair+ (suc n) -> Maybe (FinPair+ n)
    b = fin-pair+-rec₁ nothing just

    eq : Maybe (FinPair+ n) ≃ FinPair+ (suc n)
    eq = isoToEquiv (iso f b fb bf)
      where
      fb : ∀ x -> f (b x) == x
      fb (fin-pair+ zero j p) = FinPair+-path refl (sym p)
      fb (fin-pair+ (suc i) j p) = FinPair+-path refl refl

      bf : ∀ x -> b (f x) == x
      bf nothing = refl
      bf (just x) = cong just (FinPair+-path refl refl)

    step₁ :
      d CM.∙ finiteMerge CM ds ==
      finiteMerge CM (maybe d ds)
    step₁ = sym finiteMerge-Maybe

    step₂ :
      finiteMerge CM (maybe d ds) ==
      finiteMerge CM (maybe d ds ∘ fin-pair+-rec₁ nothing just)
    step₂ = finiteMerge-convert (equiv⁻¹ eq)

    step₃ : (maybe d ds ∘ fin-pair+-rec₁ nothing just) ==
            (fin-pair+-rec₁ d ds)
    step₃ = funExt
      (\{ (fin-pair+ zero j _) -> refl
        ; (fin-pair+ (suc i) j _) -> refl
        })

  finiteMerge-fin-pair+-rec₂ :
    ∀ {n : Nat} {d : D} {ds : FinPair+ n -> D} ->
      finiteMerge CM (fin-pair+-rec₂ d ds) ==
      d CM.∙ finiteMerge CM ds
  finiteMerge-fin-pair+-rec₂ {n} {d} {ds} =
    sym (step₁ >=> step₂ >=> cong (finiteMerge CM) step₃)
    where
    f : Maybe (FinPair+ n) -> FinPair+ (suc n)
    f = maybe fin-pair+-zero₂ fin-pair+-suc₂
    b : FinPair+ (suc n) -> Maybe (FinPair+ n)
    b = fin-pair+-rec₂ nothing just

    eq : Maybe (FinPair+ n) ≃ FinPair+ (suc n)
    eq = isoToEquiv (iso f b fb bf)
      where
      fb : ∀ x -> f (b x) == x
      fb (fin-pair+ i zero p) = FinPair+-path (sym p >=> +-right-zero) refl
      fb (fin-pair+ i (suc j) p) = FinPair+-path refl refl

      bf : ∀ x -> b (f x) == x
      bf nothing = refl
      bf (just x) = cong just (FinPair+-path refl refl)

    step₁ :
      d CM.∙ finiteMerge CM ds ==
      finiteMerge CM (maybe d ds)
    step₁ = sym finiteMerge-Maybe

    step₂ :
      finiteMerge CM (maybe d ds) ==
      finiteMerge CM (maybe d ds ∘ fin-pair+-rec₂ nothing just)
    step₂ = finiteMerge-convert (equiv⁻¹ eq)

    step₃ : (maybe d ds ∘ fin-pair+-rec₂ nothing just) ==
            (fin-pair+-rec₂ d ds)
    step₃ = funExt
      (\{ (fin-pair+ i zero _) -> refl
        ; (fin-pair+ i (suc j) _) -> refl
        })

module _
  {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
  {{S : Semiring ACM}}
  {{Inc : ℕ->SemiringStr S}}
  where

  binomial-theorem : (x y : D) (n : ℕ) ->
    (x + y) ^ℕ n ==
    finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))
  binomial-theorem x y zero =
    sym (
      finiteMerge-isContr isContr-FinPair+-0 >=>
      *-left ℕ->Semiring-preserves-1# >=>
      *-left-one >=>
      *-left-one)
  binomial-theorem x y (suc n) = step₁ >=> cong finiteSum (funExt step₂)
    where
    step₁ :
      (x + y) ^ℕ (suc n) ==
      (finiteSum (\fp ->
       (fin-pair+-rec₁ 0#
          (\ ((fin-pair+ i j _) : FinPair+ n) ->
             x * (ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))) fp) +
       (fin-pair+-rec₂ 0#
          (\ ((fin-pair+ i j _) : FinPair+ n) ->
             y * (ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))) fp)))
    step₁ =
      *-right (binomial-theorem x y n) >=>
      *-distrib-+-right >=>
      cong2 _+_ (sym finiteSum-* >=> sym +-left-zero >=> sym finiteMerge-fin-pair+-rec₁)
                (sym finiteSum-* >=> sym +-left-zero >=> sym finiteMerge-fin-pair+-rec₂) >=>
      sym finiteSum-+


    step₂ : ∀ fp ->
      (fin-pair+-rec₁ 0#
         (\ ((fin-pair+ i j _) : FinPair+ n) ->
            x * (ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))) fp) +
      (fin-pair+-rec₂ 0#
         (\ ((fin-pair+ i j _) : FinPair+ n) ->
            y * (ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j))) fp) ==
      (\ ((fin-pair+ i j _) : FinPair+ (suc n)) -> ℕ->Semiring (binomial-coeff' i j) * (x ^ℕ i * y ^ℕ j)) fp
    step₂ (fin-pair+ zero zero p) = zero-suc-absurd p
    step₂ (fin-pair+ zero (suc j) _) = +-left-zero >=> p₁ >=> sym p₂
      where
      p₁ : y * ((ℕ->Semiring (binomial-coeff' zero j)) * (x ^ℕ zero * y ^ℕ j)) == y ^ℕ (suc j)
      p₁ = *-right (*-left (cong ℕ->Semiring (binomial-coeff'-zero₁ j) >=>
                           ℕ->Semiring-preserves-1#) >=>
                   *-left-one >=>
                   *-left-one)

      p₂ : ℕ->Semiring (binomial-coeff' zero (suc j)) * (x ^ℕ zero * y ^ℕ (suc j)) == y ^ℕ (suc j)
      p₂ = *-left (cong ℕ->Semiring (binomial-coeff'-zero₁ (suc j)) >=>
                   ℕ->Semiring-preserves-1#) >=>
           *-left-one >=>
           *-left-one
    step₂ (fin-pair+ (suc i) zero _) = +-right-zero >=> p₁ >=> sym p₂
      where
      p₁ : x * ((ℕ->Semiring (binomial-coeff' i zero)) * (x ^ℕ i * y ^ℕ zero)) == x ^ℕ (suc i)
      p₁ = *-right (*-left (cong ℕ->Semiring (binomial-coeff'-zero₂ i) >=>
                           ℕ->Semiring-preserves-1#) >=>
                   *-left-one >=>
                   *-right-one)

      p₂ : ℕ->Semiring (binomial-coeff' (suc i) zero) * (x ^ℕ (suc i) * y ^ℕ zero) == x ^ℕ (suc i)
      p₂ = *-left (cong ℕ->Semiring (binomial-coeff'-zero₂ (suc i)) >=>
                   ℕ->Semiring-preserves-1#) >=>
           *-left-one >=>
           *-right-one
    step₂ (fin-pair+ (suc i) (suc j) _) =
      cong2 _+_ p₁ p₂ >=>
      sym *-distrib-+-right >=>
      *-left (sym (Semiringʰ.preserves-+ ℕ->Semiringʰ _ _))
      where
      p₁ : x * ((ℕ->Semiring (binomial-coeff' i (suc j))) * (x ^ℕ i * y ^ℕ (suc j))) ==
           (ℕ->Semiring (binomial-coeff' i (suc j))) * (x ^ℕ (suc i) * y ^ℕ (suc j))
      p₁ = *-commute >=> *-assoc >=> *-right (*-commute >=> sym *-assoc)
      p₂ : y * ((ℕ->Semiring (binomial-coeff' (suc i) j)) * (x ^ℕ (suc i) * y ^ℕ j)) ==
           (ℕ->Semiring (binomial-coeff' (suc i) j)) * (x ^ℕ (suc i) * y ^ℕ (suc j))
      p₂ = *-commute >=> *-assoc >=> *-right (*-assoc >=> *-right *-commute)

-}
