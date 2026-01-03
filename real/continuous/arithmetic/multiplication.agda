{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.arithmetic.multiplication where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import funext
open import heyting-field.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.distance
open import real.subspace
open import relation
open import ring
open import ring.implementations.real
open import ring.solver-equations
open import semiring
open import semiring.natural-reciprocal
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  private
    isContinuousAt-*₁-#0 : {f : D -> ℝ} {k : ℝ} {x : D} -> k # 0# -> isContinuousAt f x ->
                            isContinuousAt (\x -> k * f x) x
    isContinuousAt-*₁-#0 {f} {k} {x} k#0 cf ε⁺@(ε , 0<ε) = ∥-map handle (cf ε'⁺)
      where
      ε' : ℝ
      ε' = abs (ℝ1/ (k , k#0)) * ε
      0<ε' : 0# < ε'
      0<ε' = *-preserves-0< (eqFun abs-#0-eq ℝ1/-#0) 0<ε
      ε'⁺ : ℝ⁺
      ε'⁺ = ε' , 0<ε'
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε'⁺ (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (k * f x) (k * f y))
      handle (δ , δ-close) = (δ , δ-close')
        where
        δ-close' : ∀ y -> εClose δ x y -> εClose ε⁺ (k * f x) (k * f y)
        δ-close' y dxy<δ = subst2 _<_ akd=d' akε'=ε akd<akε'
          where
          d<ε' : distance (f x) (f y) < ε'
          d<ε' = δ-close y dxy<δ

          akd<akε' : (abs k * distance (f x) (f y)) < (abs k * ε')
          akd<akε' = *₁-preserves-< (eqFun abs-#0-eq k#0) d<ε'

          akd=d' : abs k * distance (f x) (f y) == distance (k * f x) (k * f y)
          akd=d' = sym abs-distrib-* >=> cong abs *-distrib-diff-left

          akε'=ε : abs k * ε' == ε
          akε'=ε =
            sym *-assoc >=>
            *-left (sym abs-distrib-* >=>
                    cong abs (*-commute >=> ℝ1/-inverse) >=>
                    abs-0≤-path (weaken-< 0<1)) >=>
            *-left-one

    isContinuousAt-*₁-<1 : {f : D -> ℝ} {k : ℝ} {x : D} -> abs k < 1# -> isContinuousAt f x ->
                         isContinuousAt (\x -> k * f x) x
    isContinuousAt-*₁-<1 {f} {k} {x} ak<1 cf ε⁺@(ε , 0<ε) = ∥-map handle (cf ε⁺)
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (k * f x) (k * f y))
      handle (δ , δ-close) = (δ , δ-close')
        where
        δ-close' : ∀ y -> εClose δ x y -> εClose ε⁺ (k * f x) (k * f y)
        δ-close' y dxy<δ = trans-≤-< (trans-=-≤ (sym akd=d') akd≤d) d<ε
          where
          d<ε : distance (f x) (f y) < ε
          d<ε = δ-close y dxy<δ

          akd≤d : (abs k * distance (f x) (f y)) ≤ distance (f x) (f y)
          akd≤d =
            trans-≤-= (*₂-preserves-≤ (weaken-< ak<1) (0≤distanceᵉ (f x) (f y)))
                      *-left-one

          akd=d' : abs k * distance (f x) (f y) == distance (k * f x) (k * f y)
          akd=d' = sym abs-distrib-* >=> cong abs *-distrib-diff-left

  opaque
    isContinuousAt-*₁ : {f : D -> ℝ} {k : ℝ} {x : D} -> isContinuousAt f x ->
                        isContinuousAt (\x -> k * f x) x
    isContinuousAt-*₁ {f} {k} {x} cf =
      unsquash (isProp-isContinuousAt (\x -> k * f x))
        (∥-map handle (split-distance<ε 0# k (1# , 0<1)))
      where
      handle : Tri⊎ (k < 0#) (distance 0# k < 1#) (0# < k) ->
               isContinuousAt (\x -> k * f x) x
      handle (tri⊎-< k<0) = isContinuousAt-*₁-#0 (inj-l k<0) cf
      handle (tri⊎-> 0<k) = isContinuousAt-*₁-#0 (inj-r 0<k) cf
      handle (tri⊎-= d0k<1) = isContinuousAt-*₁-<1 (trans-=-< (cong abs (sym diff0-path)) d0k<1) cf

    isContinuousAt-*₂ : {f : D -> ℝ} {k : ℝ} {x : D} -> isContinuousAt f x ->
                        isContinuousAt (\x -> f x * k) x
    isContinuousAt-*₂ cf =
      subst2 isContinuousAt (funExt (\x -> *-commute)) refl (isContinuousAt-*₁ cf)


    isContinuous-*₁ : {f : D -> ℝ} {k : ℝ} -> isContinuous f ->
                      isContinuous (\x -> k * f x)
    isContinuous-*₁ {f} {k} (isContinuous-cons cf) .isContinuous.at x = isContinuousAt-*₁ (cf x)

    isContinuous-*₂ : {f : D -> ℝ} {k : ℝ} -> isContinuous f ->
                      isContinuous (\x -> f x * k)
    isContinuous-*₂ {f} {k} (isContinuous-cons cf) .isContinuous.at x = isContinuousAt-*₂ (cf x)

    isContinuousAt-* : {f g : D -> ℝ} {x : D} -> isContinuousAt f x -> isContinuousAt g x ->
                     isContinuousAt (\x -> f x * g x) x
    isContinuousAt-* {f} {g} {x} cf cg ε⁺@(ε , 0<ε) =
      ∥-map4 handle ((isContinuousAt-*₂ cf) ε/4⁺) ((isContinuousAt-*₁ cg) ε/4⁺)
                    (cf sqrt-ε/2⁺) (cg sqrt-ε/2⁺)
      where
      ε/2 ε/4 : ℝ
      ε/2 = ε * 1/2
      ε/4 = ε/2 * 1/2
      0<ε/2 : 0# < ε/2
      0<ε/2 = *-preserves-0< 0<ε 0<1/2
      0<ε/4 : 0# < ε/4
      0<ε/4 = *-preserves-0< 0<ε/2 0<1/2
      ε/2⁺ : ℝ⁺
      ε/2⁺ = ε/2 , 0<ε/2
      ε/4⁺ : ℝ⁺
      ε/4⁺ = ε/4 , 0<ε/4
      sqrt-ε/2 : ℝ
      sqrt-ε/2 = sqrtℝ (ε/2 , (weaken-< 0<ε/2))
      0<sqrt-ε/2 : 0# < sqrt-ε/2
      0<sqrt-ε/2 = sqrt-0< (ε/2 , weaken-< 0<ε/2) 0<ε/2
      sqrt-ε/2⁺ : ℝ⁺
      sqrt-ε/2⁺ = sqrt-ε/2 , 0<sqrt-ε/2

      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε/4⁺ (f x * g x) (f y * g x)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε/4⁺ (f x * g x) (f x * g y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose sqrt-ε/2⁺ (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose sqrt-ε/2⁺ (g x) (g y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (f x * g x) (f y * g y))
      handle ((δ1 , 0<δ1) , δ1-close) ((δ2 , 0<δ2) , δ2-close)
             ((δ3 , 0<δ3) , δ3-close) ((δ4 , 0<δ4) , δ4-close) = δ⁺ , δ-close
        where
        δ : ℝ
        δ = min (min δ1 δ2) (min δ3 δ4)
        δ⁺ : ℝ⁺
        δ⁺ = δ , min-greatest-< (min-greatest-< 0<δ1 0<δ2) (min-greatest-< 0<δ3 0<δ4)

        δ-close : ∀ y -> εClose δ⁺ x y -> εClose ε⁺ (f x * g x) (f y * g y)
        δ-close y dxy<δ =
          trans-≤-< lt1
            (trans-<-=
              (+-preserves-< (+-preserves-< (δ1-close y dxy<δ1) (δ2-close y dxy<δ2)) lt-d*)
              ((cong2 _+_ +-/2-path (sqrt² _)) >=> +-/2-path))
          where
          dxy<δ1 : distance x y < δ1
          dxy<δ1 = trans-<-≤ dxy<δ (trans-≤ min-≤-left min-≤-left)
          dxy<δ2 : distance x y < δ2
          dxy<δ2 = trans-<-≤ dxy<δ (trans-≤ min-≤-left min-≤-right)
          dxy<δ3 : distance x y < δ3
          dxy<δ3 = trans-<-≤ dxy<δ (trans-≤ min-≤-right min-≤-left)
          dxy<δ4 : distance x y < δ4
          dxy<δ4 = trans-<-≤ dxy<δ (trans-≤ min-≤-right min-≤-right)
          lt1 : distance (f x * g x) (f y * g y) ≤
                ((distance (f x * g x) (f y * g x) + distance (f x * g x) (f x * g y)) +
                 (distance (f x) (f y)) * (distance (g x) (g y)))
          lt1 = trans-=-≤ (cong abs diff-*-expand)
                 (trans-≤ abs-distrib-+
                   (+-preserves-≤ abs-distrib-+ (path-≤ abs-distrib-*)))
          lt-d* : (distance (f x) (f y) * distance (g x) (g y)) < (sqrt-ε/2 * sqrt-ε/2)
          lt-d* = trans-≤-< (*₁-preserves-≤ (0≤distanceᵉ (f x) (f y)) (weaken-< (δ4-close y dxy<δ4)))
                            (*₂-preserves-< (δ3-close y dxy<δ3) 0<sqrt-ε/2)

    isContinuous-* : {f g : D -> ℝ} -> isContinuous f -> isContinuous g ->
                     isContinuous (\x -> f x * g x)
    isContinuous-* {f} {g} (isContinuous-cons cf) (isContinuous-cons cg) .isContinuous.at x =
      isContinuousAt-* (cf x) (cg x)
