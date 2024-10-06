{-# OPTIONS --cubical --safe --exact-split #-}

module ring.exponentiation.diff where

open import additive-group
open import base
open import commutative-monoid
open import equality
open import fin.sum-pair
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.sum-pair
open import finite-commutative-monoid.without-point
open import finset.instances.sum-pair
open import finset.without-point
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import nat
open import ring
open import semiring
open import semiring.exponentiation
open import without-point


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}} where
  private
    instance
      IACM = ACM

    CM : CommMonoid D
    CM = CommMonoid-+ D

  opaque
    diff*all-ones-path : {a b : D} {n : ℕ} ->
      (diff a b) * finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> a ^ℕ i * b ^ℕ j) ==
      (diff (a ^ℕ (suc n)) (b ^ℕ (suc n)))
    diff*all-ones-path {a} {b} {n} =
      *-distrib-+-right >=>
      +-cong (sym finiteSum-* >=> sym p2) (sym finiteSum-* >=> sym p1) >=>
      sym (finiteMerge-split _) >=>
      p3
      where
      af : FinPair+ n -> D
      af (fin-pair+ i j _) = (- a) * (a ^ℕ i * b ^ℕ j)
      af' : FinPair+ (suc n) -> D
      af' = fin-pair+-rec₁ 0# af
      bf : FinPair+ n -> D
      bf (fin-pair+ i j _) = b * (a ^ℕ i * b ^ℕ j)
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

      p-zero₁ : bf' fin-pair+-zero₁ + af' fin-pair+-zero₁ == b ^ℕ (suc n)
      p-zero₁ = +-right-zero >=> *-right *-left-one
      p-zero₂ : bf' fin-pair+-zero₂ + af' fin-pair+-zero₂ == - (a ^ℕ (suc n))
      p-zero₂ = +-left-zero >=> *-right *-right-one  >=> minus-extract-left
      p-suc : ∀ (ij : FinPair+ (suc n)) ->
                ij != fin-pair+-zero₁ -> ij != fin-pair+-zero₂ ->
                bf' ij + af' ij == 0#
      p-suc (fin-pair+ zero _ _)          ¬p₁ ¬p₂ = bot-elim (¬p₁ (FinPair+-path₁ refl))
      p-suc (fin-pair+ (suc i) zero _)    ¬p₁ ¬p₂ = bot-elim (¬p₂ (FinPair+-path₂ refl))
      p-suc (fin-pair+ (suc i) (suc j) _) ¬p₁ ¬p₂ =
        +-cong (*-right *-commute >=> sym *-assoc >=> *-commute)
               (sym *-assoc >=> *-left minus-extract-left >=> minus-extract-left) >=>
        +-inverse

      zero₂!=zero₁ : ¬ (Path (FinPair+ (suc n)) fin-pair+-zero₂ fin-pair+-zero₁)
      zero₂!=zero₁ p = zero-suc-absurd (cong FinPair+.j p)

      p3 : finiteSum (\ij -> bf' ij + af' ij) ==
           (diff (a ^ℕ (suc n)) (b ^ℕ (suc n)))
      p3 =
        finiteMerge-WithoutPoint CM fin-pair+-zero₁ (\ij -> bf' ij + af' ij) >=>
        +-left p-zero₁ >=>
        +-right (finiteMerge-WithoutPoint CM (fin-pair+-zero₂ , zero₂!=zero₁)
                  (\(ij , _) -> bf' ij + af' ij) >=>
                 +-left p-zero₂ >=>
                 +-right (finiteMerge-ε CM (\ ((ij , ¬p₁) , ¬p₂) ->
                                              p-suc ij ¬p₁ (¬p₂ ∘ WithoutPoint-path))) >=>
                 +-right-zero)
