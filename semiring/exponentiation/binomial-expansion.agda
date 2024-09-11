{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.exponentiation.binomial-expansion where

open import additive-group
open import base
open import combinatorics.binomial-coefficients
open import equality
open import fin.sum-pair
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finite-commutative-monoid.sum-pair
open import finset.instances.sum-pair
open import finsum
open import finsum.arithmetic
open import funext
open import nat
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  opaque
    binomial-expansion-path : ∀ (a b : D) (n : ℕ) ->
      (a + b) ^ℕ n == finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) ->
                                   (ℕ->Semiring (binomial-coeff' i j)) * (a ^ℕ i * b ^ℕ j))
    binomial-expansion-path a b zero =
      sym (finiteMerge-isContr _ isContr-FinPair+-0 _ >=>
           *-right *-right-one >=> *-right-one >=>
           ℕ->Semiring-preserves-1#)
    binomial-expansion-path a b (suc n) =
      *-right (binomial-expansion-path a b n) >=>
      *-distrib-+-right >=>
      +-cong (sym finiteSum-* >=> sym p1) (sym finiteSum-* >=> sym p2) >=>
      sym (finiteMerge-split (CommMonoid-+ _)) >=>
      cong finiteSum (funExt p3)
      where
      af : FinPair+ n -> D
      af (fin-pair+ i j _) = a * ((ℕ->Semiring (binomial-coeff' i j)) * (a ^ℕ i * b ^ℕ j))
      af' : FinPair+ (suc n) -> D
      af' = fin-pair+-rec₁ 0# af
      bf : FinPair+ n -> D
      bf (fin-pair+ i j _) = b * ((ℕ->Semiring (binomial-coeff' i j)) * (a ^ℕ i * b ^ℕ j))
      bf' : FinPair+ (suc n) -> D
      bf' = fin-pair+-rec₂ 0# bf

      p1 : finiteSum af' == finiteSum af
      p1 = finiteMerge-FinPair+-split₁ _ af' >=>
           +-left-zero >=>
           cong finiteSum (funExt (\x -> fin-pair+-rec₁-suc 0# af x))

      p2 : finiteSum bf' == finiteSum bf
      p2 = finiteMerge-FinPair+-split₂ _ bf' >=>
           +-left-zero >=>
           cong finiteSum (funExt (\x -> fin-pair+-rec₁-suc 0# bf x))

      p3 : ∀ (ij@(fin-pair+ i j _) : FinPair+ (suc n)) ->
        (af' ij + bf' ij) ==
        (ℕ->Semiring (binomial-coeff' i j)) * (a ^ℕ i * b ^ℕ j)
      p3 (fin-pair+ zero zero p) = zero-suc-absurd p
      p3 (fin-pair+ (suc i) zero p) =
        +-right-zero >=>
        sym *-assoc >=> *-left *-commute >=> *-assoc >=>
        *-cong (cong ℕ->Semiring (binomial-coeff'-zero₂ i))
               (sym *-assoc)
      p3 (fin-pair+ zero (suc j) p) =
        +-left-zero >=>
        sym *-assoc >=> *-left *-commute >=> *-assoc >=>
        *-cong (cong ℕ->Semiring (binomial-coeff'-zero₁ j))
               (sym *-assoc >=> *-left *-commute >=> *-assoc)
      p3 (fin-pair+ (suc i) (suc j) p) =
        +-cong
          (sym *-assoc >=> *-left *-commute >=> *-assoc >=>
           *-right (sym *-assoc))
          (sym *-assoc >=> *-left *-commute >=> *-assoc >=>
           *-right (sym *-assoc >=> *-left *-commute >=> *-assoc)) >=>
        (sym *-distrib-+-right) >=>
        *-left (sym (Semiringʰ.preserves-+ (∃!-prop ∃!ℕ->Semiring) _ _))
