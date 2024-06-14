{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3.addition where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import metric-space
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative3
open import real.derivative3.slope
open import real.epsilon-bounded
open import real.rational
open import real.sequence.limit
open import real.sequence.limit-point
open import real.sequence.limit.arithmetic
open import ring.implementations.real
open import semiring
open import sequence
open import subset
open import subset.subspace
open import truncation

private
  distance-+-swap : {a b c d : ℝ} -> distance (a + b) (c + d) ≤ (distance a c + distance b d)
  distance-+-swap {a} {b} {c} {d} =
    trans-≤-= (distance-triangleᵉ (a + b) (c + b) (c + d)) (+-cong d1 d2)
    where
    d1 : distance (a + b) (c + b) == distance a c
    d1 = cong abs (sym (+₂-preserves-diff))
    d2 : distance (c + b) (c + d) == distance b d
    d2 = cong abs (sym (+₁-preserves-diff))


module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f f' g g' : Subspace S -> ℝ}
         (df : isDerivative S f f') (dg : isDerivative S g g') where

  {-
  isDerivative-+ : isDerivative S (\x -> f x + g x) (\x -> f' x + g' x)
  isDerivative-+ x∈         .isDerivativeAt.limit-point = isDerivativeAt.limit-point (df x∈)
  isDerivative-+ x∈@(x , _) .isDerivativeAt.distance<ε (ε , 0<ε) =

    ∥-map2 handle (isDerivativeAt.distance<ε (df x∈) (ε/2 , 0<ε/2))
                  (isDerivativeAt.distance<ε (dg x∈) (ε/2 , 0<ε/2))
    where
    ε/2 = 1/2 * ε
    0<ε/2 = *-preserves-0< 0<1/2 0<ε
    handle : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) -> (y#x : y # x) -> distance y x < δ ->
               distance (slope S (\a -> f a) y∈ x∈ y#x) (f' x∈) < ε/2) ->
             (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) -> (y#x : y # x) -> distance y x < δ ->
               distance (slope S (\a -> g a) y∈ x∈ y#x) (g' x∈) < ε/2) ->
             (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) -> (y#x : y # x) -> distance y x < δ ->
               distance (slope S (\a -> f a + g a) y∈ x∈ y#x) (f' x∈ + g' x∈) < ε)
    handle ((δf , 0<δf) , close-f) ((δg , 0<δg) , close-g) = (δ , 0<δ) , close
      where
      δ : ℝ
      δ = min δf δg
      0<δ : 0# < δ
      0<δ = min-greatest-< 0<δf 0<δg

      close : (y∈@(y , _) : ∈-Subtype S) -> (y#x : y # x) -> distance y x < δ ->
              distance (slope S (\a -> f a + g a) y∈ x∈ y#x) (f' x∈ + g' x∈) < ε
      close y∈ y#x d<δ =
        trans-≤-< distance-lt
          (trans-<-= (+-preserves-< (close-f y∈ y#x (trans-<-≤ d<δ min-≤-left))
                                    (close-g y∈ y#x (trans-<-≤ d<δ min-≤-right)))
                     1/2-path)
        where
        slope-path : (slope S (\a -> f a + g a) y∈ x∈ y#x) ==
                     (slope S (\a -> f a) y∈ x∈ y#x) + (slope S (\a -> g a) y∈ x∈ y#x)
        slope-path = *-left (sym +-swap-diff) >=> *-distrib-+-right

        distance-lt :
          distance (slope S (\a -> f a + g a) y∈ x∈ y#x) (f' x∈ + g' x∈) ≤
          (distance (slope S (\a -> f a) y∈ x∈ y#x) (f' x∈) +
           distance (slope S (\a -> g a) y∈ x∈ y#x) (g' x∈))
        distance-lt = trans-=-≤ (cong2 distance slope-path refl) distance-+-swap
  -}


  -- isDerivative-+' : isDerivative S (\x -> f x + g x) (\x -> f' x + g' x)
  -- isDerivative-+' =
  --   isContinuousSlope->isDerivative S
  --     (isDifferentiable->NoIsolatedPoints (f' , df))
  --     (\x -> f x + g x) ?
  --     ? ?
