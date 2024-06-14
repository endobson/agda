{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3.slope where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import heyting-field.instances.real
open import nat
open import metric-space
open import metric-space.instances.real
open import metric-space.instances.subspace
open import metric-space.continuous
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import real
open import real.derivative3
open import real.apartness
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.subspace
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation

NoIsolatedPoints : {ℓS : Level} (S : Subtype ℝ ℓS) -> Type (ℓ-max ℓS ℓ-one)
NoIsolatedPoints S = ∀ ((x , _) : Subspace S) -> isLimitPoint S x

NoIsolatedPoints-UnivS : NoIsolatedPoints (UnivS ℝ)
NoIsolatedPoints-UnivS (x , _) = isLimitPoint-UnivS x

isDifferentiable->NoIsolatedPoints : {ℓS : Level} {S : Subtype ℝ ℓS}
                                     {f : Subspace S -> ℝ} -> isDifferentiable S f ->
                                     NoIsolatedPoints S
isDifferentiable->NoIsolatedPoints (_ , d) x =
  isDerivativeAt.limit-point (d x)


module _ {ℓS : Level} (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) (g : Subspace S -> Subspace S -> ℝ) where
  isSlope : Type (ℓ-max ℓS ℓ-one)
  isSlope = ∀ (x∈@(x , _) y∈@(y , _) : Subspace S) -> (g x∈ y∈) * diff x y == diff (f x∈) (f y∈)

module _ {ℓS : Level} (S : Subtype ℝ ℓS) (limit-points : NoIsolatedPoints S)
         (f : Subspace S -> ℝ) (g : Subspace S -> Subspace S -> ℝ) where
  isContinuousSlope->isDerivative :
    (∀ x -> isContinuous (g x)) -> isSlope S f g -> isDerivative S f (\x -> g x x)
  isContinuousSlope->isDerivative gc isSlope-g x∈@(x , _)
    .isDerivativeAt.limit-point = limit-points x∈
  isContinuousSlope->isDerivative gc isSlope-g x∈@(x , _)
    .isDerivativeAt.distance<ε ε⁺@(ε , 0<ε) =
      ∥-map handle (gc x∈ .isContinuous.at x∈ ε⁺)
      where
      handle : Σ[ (δ , _) ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) ->
                                  distance x y < δ ->
                                  distance (g x∈ x∈) (g x∈ y∈) < ε) ->
               Σ[ (δ , _) ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> (x#y : x # y) ->
                                  distance x y < δ ->
                                  distance (slope S f x∈ y∈ x#y) (g x∈ x∈) < ε)
      handle (δ⁺@(δ , 0<δ) , close-g) = δ⁺ , close
        where
        close : ∀ (y∈@(y , _) : Subspace S) -> (x#y : x # y) ->
                  distance x y < δ ->
                  distance (slope S f x∈ y∈ x#y) (g x∈ x∈) < ε
        close y∈@(y , _) x#y dxy<δ = ans
          where
          path1 : (diff (f x∈) (f y∈) * 1/diff x#y) == (g x∈ y∈)
          path1 = *-left (sym (isSlope-g x∈ y∈)) >=>
                  *-assoc >=> (*-right (*-commute >=> ℝ1/-inverse _ _)) >=>
                  *-right-one
          lt1 : distance (g x∈ x∈) (g x∈ y∈) < ε
          lt1 = close-g y∈ dxy<δ

          ans : distance (diff (f x∈) (f y∈) * 1/diff x#y) (g x∈ x∈) < ε
          ans = trans-=-< (cong2 distance path1 refl >=> distance-commuteᵉ _ (g x∈ x∈)) lt1
