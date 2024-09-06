{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.instances.power-series where

open import additive-group
open import additive-group.instances.power-series
open import base
open import equality-path
open import fin.sum-pair
open import fin.sum-triple
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finite-commutative-monoid.sum-pair
open import finset.instances.sum-pair
open import finset.instances.sum-triple
open import finsum
open import finsum.arithmetic
open import finsum.sigma
open import funext
open import nat
open import power-series
open import semiring

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

    1-PS : PowerSeries D
    1-PS .PowerSeries.seq zero = 1#
    1-PS .PowerSeries.seq (suc n) = 0#

    *-PS : PowerSeries D -> PowerSeries D -> PowerSeries D
    *-PS (power-series f) (power-series g) = power-series h
      where
      h : ℕ -> D
      h n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> f i * g j)

    opaque
      *-PS-left-zero : {p : PowerSeries D} -> *-PS 0# p == 0#
      *-PS-left-zero {power-series f} = PowerSeries-path inner
        where
        inner : (n : Nat) -> finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> 0# * f j) == 0#
        inner n = finiteMerge-ε _ (\ _ -> *-left-zero)

      *-PS-left-one : {p : PowerSeries D} -> *-PS 1-PS p == p
      *-PS-left-one {power-series f} = PowerSeries-path inner
        where
        f₁ : Nat -> D
        f₁ = PowerSeries.seq 1-PS

        inner : (n : Nat) -> finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> f₁ i * f j) == f n
        inner zero =
          finiteMerge-isContr _ isContr-FinPair+-0 _ >=>
          *-left-one
        inner (suc n) =
          finiteMerge-FinPair+-split₁ _ _ >=>
          +-left *-left-one >=>
          +-right (finiteMerge-ε _ (\_ -> *-left-zero)) >=>
          +-right-zero

      *-PS-commute : {p1 p2 : PowerSeries D} -> *-PS p1 p2 == *-PS p2 p1
      *-PS-commute =
        PowerSeries-path (\n ->
          finiteMerge-convert-iso _ FinPair+-swap _ >=>
          cong finiteSum (funExt (\_ -> *-commute)))

      *-PS-distrib-+-right : {p1 p2 p3 : PowerSeries D} ->
        *-PS (p1 + p2) p3 == *-PS p1 p3 + *-PS p2 p3
      *-PS-distrib-+-right =
        PowerSeries-path (\n ->
          cong finiteSum (funExt (\_ -> *-distrib-+-right)) >=>
          finiteMerge-split _)

      *-PS-assoc : {p1 p2 p3 : PowerSeries D} -> *-PS (*-PS p1 p2) p3 == *-PS p1 (*-PS p2 p3)
      *-PS-assoc {power-series f1} {power-series f2} {power-series f3} =
        PowerSeries-path (\n -> dir2 n >=> triple-path n >=> sym (dir1 n))
        where
        triple1 : ℕ -> D
        triple1 n = finiteSum (\ ((fin-triple+ i j k _) : FinTriple+ n) -> f1 i * (f2 j * f3 k))
        triple2 : ℕ -> D
        triple2 n = finiteSum (\ ((fin-triple+ i j k _) : FinTriple+ n) -> (f1 i * f2 j) * f3 k)

        dir1 : (n : ℕ) ->
          finiteSum (\ ((fin-pair+ i jk _) : FinPair+ n) ->
                       f1 i * (finiteSum (\ ((fin-pair+ j k _) : FinPair+ jk) -> f2 j * f3 k))) ==
          triple1 n
        dir1 n =
          cong finiteSum (funExt (\_ -> sym finiteSum-*)) >=>
          sym (finiteSum-Σ _ _ _) >=>
          finiteMergeᵉ-convert-iso _ _ _ FinTriple+-split₁ _

        dir2 : (n : ℕ) ->
          finiteSum (\ ((fin-pair+ ij k _) : FinPair+ n) ->
                       (finiteSum (\ ((fin-pair+ i j _) : FinPair+ ij) -> f1 i * f2 j)) * f3 k) ==
          triple2 n
        dir2 n =
          cong finiteSum (funExt (\_ -> *-commute >=> sym finiteSum-* >=>
                                        cong finiteSum (funExt (\_ -> *-commute)))) >=>
          sym (finiteSum-Σ _ _ _) >=>
          finiteMergeᵉ-convert-iso _ _ _ FinTriple+-split₂ _

        triple-path : (n : ℕ) -> triple2 n == triple1 n
        triple-path n = cong finiteSum (funExt (\_ -> *-assoc))

  instance
    Semiring-PS : Semiring AdditiveCommMonoid-PS
    Semiring-PS = record
      { 1# = 1-PS
      ; _*_ = *-PS
      ; *-assoc = *-PS-assoc
      ; *-commute = *-PS-commute
      ; *-left-zero = *-PS-left-zero
      ; *-left-one = *-PS-left-one
      ; *-distrib-+-right = *-PS-distrib-+-right
      ; isSet-Domain = isSet-PowerSeries (AdditiveCommMonoid.isSet-Domain ACM)
      }
