{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.overlap-at-point where

open import additive-group
open import additive-group.instances.real
open import base
open import equality-path
open import hlevel
open import isomorphism
open import order
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.continuous.arithmetic
open import real.gluing.overlap-at-zero
open import real.gluing.overlap-at-zero.extension
open import real.gluing.overlap-at-zero.continuous
open import real.subspace
open import sigma
open import sigma.base
open import subset
open import subset.subspace
open import truncation
open import univalence

module _ (a : ℝ) (f : (x : ℝ≤≥ a) -> ℝ) (cont-f@(isContinuous-cons cf) : isContinuous f)  where
   private
     lift-≤≥0 : {x : ℝ} -> x ≤≥ 0# -> (x + a) ≤≥ a
     lift-≤≥0 {x} x≤≥0 = ∥-map handle x≤≥0
       where
       handle : (x ≤ 0#) ⊎ (0# ≤ x) -> ((x + a) ≤ a) ⊎ (a ≤ (x + a))
       handle (inj-l x≤0) = inj-l (trans-≤-= (+₂-preserves-≤ x≤0) +-left-zero)
       handle (inj-r 0≤x) = inj-r (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ 0≤x))

     lower-≤≥a : {x : ℝ} -> x ≤≥ a -> (x + (- a)) ≤≥ 0#
     lower-≤≥a {x} x≤≥a = ∥-map handle x≤≥a
       where
       handle : (x ≤ a) ⊎ (a ≤ x) -> ((x + (- a)) ≤ 0#) ⊎ (0# ≤ (x + (- a)))
       handle (inj-l x≤a) = inj-l (diff-≤0⁺ x≤a)
       handle (inj-r a≤x) = inj-r (diff-0≤⁺ a≤x)

     f' : ℝ≤≥0 -> ℝ
     f' (x , x≤≥0) = f (x + a , lift-≤≥0 x≤≥0)


     cont-f' : isContinuous f'
     cont-f' .isContinuous.at x∈@(x , x≤≥0) = ans
       where
       xa : ℝ
       xa = x + a
       xa≤≥a : xa ≤≥ a
       xa≤≥a = lift-≤≥0 x≤≥0
       xa∈ : ℝ≤≥ a
       xa∈ = xa , xa≤≥a

       ans : isContinuousAt f' x∈
       ans ε⁺@(ε , _) = ∥-map handle (cf xa∈ ε⁺)
         where
         handle :
           Σ[ (δ , _) ∈ ℝ⁺ ] (∀ (y∈@(y , _) : (ℝ≤≥ a)) ->
                              distance xa y < δ -> distance (f xa∈) (f y∈) < ε) ->
           Σ[ (δ , _) ∈ ℝ⁺ ] (∀ (y∈@(y , _) : (ℝ≤≥ 0#)) ->
                              distance x y < δ -> distance (f' x∈) (f' y∈) < ε)
         handle (δ⁺@(δ , _) , close) = (δ⁺ , close')
           where
           close' : (∀ (y∈@(y , _) : (ℝ≤≥ 0#)) ->
                       distance x y < δ -> distance (f' x∈) (f' y∈) < ε)
           close' (y , y≤≥0) dxy<δ = close (y + a , lift-≤≥0 y≤≥0) dxaya<δ
             where
             dxaya<δ : distance (x + a) (y + a) < δ
             dxaya<δ =
               trans-=-< (cong abs (sym +-swap-diff >=> +-right +-inverse >=> +-right-zero))
                 dxy<δ

   opaque
     extend-≤≥ : ℝ -> ℝ
     extend-≤≥ x = extend-≤≥0 f' cont-f' (x + (- a))

     isExtension-extend-≤≥ : ∀ (x∈@(x , _) : (ℝ≤≥ a)) -> extend-≤≥ x == f x∈
     isExtension-extend-≤≥ (x , x≤≥a) =
       isExtension-extend-≤≥0 f' cont-f' (x + (- a) , lower-≤≥a x≤≥a) >=>
       cong f (Subspace-path (+-commute >=> diff-step))

     isContinuous-extend-≤≥ : isContinuous extend-≤≥
     isContinuous-extend-≤≥ =
       ∘-isContinuous
         (isContinuous-extend-≤≥0 f' cont-f')
         (isContinuous-+₂ isContinuous-id)
