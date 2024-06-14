{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.extend-to-zero where

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
open import heyting-field.instances.rational
open import nat
open import order
open import metric-space
open import metric-space.continuous
open import metric-space.instances.subspace
open import metric-space.instances.real
open import order.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-field
open import ordered-field.mean
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import real.derivative3
open import real.derivative3.slope
open import real.apartness
open import real.order
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.subspace
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation

module _
  (f : (x : ℝ⁺) -> ℝ)
  (cont-f : isContinuous f)
  {lim : ℝ}
  (isLimit-lim : isLimitAt ℝ⁺S f 0# lim)
  ((x , 0≤x) : ℝ⁰⁺)
  where

  private
    fℚ : ℚ⁺ -> ℝ
    fℚ (q , 0<q) = (f (ℚ->ℝ q , ℚ->ℝ-preserves-< 0<q))
    module lim = Real lim
    module x = Real x

    L'ε : Pred ℚ ℓ-zero
    L'ε q = Σ[ q' ∈ ℚ ] Σ[ q<q' ∈ q < q' ] Σ[ (δ , _) ∈ ℚ⁺ ]
              (Real.U (distance 0# x) δ ×
               ∀ (t⁺@(t , _) : ℚ⁺) -> Real.U (distance 0# (ℚ->ℝ t)) δ -> (Real.L (fℚ t⁺) q'))
    L'0< : Pred ℚ ℓ-zero
    L'0< q = Σ[ xL-0 ∈ x.L 0# ] (Real.L (f (x , (L->ℝ< xL-0))) q)
    L' : Pred ℚ ℓ-zero
    L' q = L'ε q ⊎ L'0< q
    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥

    U'ε : Pred ℚ ℓ-zero
    U'ε q = Σ[ q' ∈ ℚ ] Σ[ q'<q ∈ q' < q ] Σ[ (δ , _) ∈ ℚ⁺ ]
              (Real.U (distance 0# x) δ ×
               ∀ (t⁺@(t , _) : ℚ⁺) -> Real.U (distance 0# (ℚ->ℝ t)) δ -> (Real.U (fℚ t⁺) q'))
    U'0< : Pred ℚ ℓ-zero
    U'0< q = Σ[ xL-0 ∈ x.L 0# ] (Real.U (f (x , (L->ℝ< xL-0))) q)
    U' : Pred ℚ ℓ-zero
    U' q = U'ε q ⊎ U'0< q
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥


{-
    isLowerSet-L : isLowerSet L
    isLowerSet-L {q} {r} q<r = ∥-map handle
      where
      handle : L' r -> L' q
      handle (inj-r (xL0 , fLr)) = inj-r (xL0 , Real.isLowerSet-L (f _) q<r fLr)
      handle (inj-l (r' , r<r' , δ⁺ , dxU-δ , close-L)) =
        inj-l (r , q<r , δ⁺ , dxU-δ ,
               (\t dt<δ -> Real.isLowerSet-L (f _) r<r' (close-L t dt<δ)))

    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r = ∥-map handle
      where
      handle : U' q -> U' r
      handle (inj-r (xL0 , fUr)) = inj-r (xL0 , Real.isUpperSet-U (f _) q<r fUr)
      handle (inj-l (q' , q'<q , δ⁺ , dxU-δ , close-U)) =
        inj-l (q , q<r , δ⁺ , dxU-δ ,
               (\t dt<δ -> Real.isUpperSet-U (f _) q'<q (close-U t dt<δ)))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] ((q < r) × L r)
      handle (inj-r (xL0 , fxLq)) = ∥-map handle2 (Real.isUpperOpen-L (f _) q fxLq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((q < r) × Real.L (f _) r) -> Σ[ r ∈ ℚ ] ((q < r) × L r)
        handle2 (r , q<r , fLr) = r , q<r , ∣ inj-r (_ , fLr) ∣
      handle (inj-l  (q' , q<q' , δ⁺ , dU-δ , close-L)) =
        ∣ mean q q' , mean-<₁ q<q' ,
          ∣ inj-l (q' , mean-<₂ q<q' , δ⁺ , dU-δ , close-L) ∣ ∣


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' q -> ∃[ r ∈ ℚ ] ((r < q) × U r)
      handle (inj-r (xL0 , fxUq)) = ∥-map handle2 (Real.isLowerOpen-U (f _) q fxUq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((r < q) × Real.U (f _) r) -> Σ[ r ∈ ℚ ] ((r < q) × U r)
        handle2 (r , r<q , fUr) = r , r<q , ∣ inj-r (xL0 , fUr) ∣
      handle (inj-l (q' , q'<q , δ⁺ , dU-δ , close-U)) =
        ∣ mean q' q , mean-<₂ q'<q ,
          ∣ inj-l (q' , mean-<₁ q'<q , δ⁺ , dU-δ , close-U) ∣ ∣

-}
