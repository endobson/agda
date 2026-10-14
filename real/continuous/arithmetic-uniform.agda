{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.arithmetic-uniform where

open import additive-group
open import additive-group.instances.real
open import base
open import nat
open import equivalence
open import fin
open import funext
open import functions
open import finite-commutative-monoid
open import equality
open import heyting-field.instances.real
open import metric-space
open import metric-space.ball-subspace
open import metric-space.continuous
open import metric-space.uniformly-continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import ordered-additive-group.absolute-value
open import nat.order
open import finset
open import finsum
open import order.instances.real
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import real
open import real.distance
open import real.subspace
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import subset.subspace
open import truncation


module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isUniformlyContinuous-minus :
      {f : D -> ℝ} -> isUniformlyContinuous f -> isUniformlyContinuous (\x -> - (f x))
    isUniformlyContinuous-minus {f} (isUniformlyContinuous-cons cf)
      .isUniformlyContinuous.close ε⁺@(ε , 0<ε) =
      ∥-map handle (cf ε⁺)
      where

      handle :
        Σ[ δ₁ ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δ₁ x₁ x₂ -> εClose ε⁺ (f x₁) (f x₂)) ->
        Σ[ δ₃ ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δ₃ x₁ x₂ -> εClose ε⁺ (- (f x₁)) (- (f x₂)))
      handle (δ , f-close) = (δ , \x₁ x₂ c -> trans-=-< d-path (f-close x₁ x₂ c))
        where
        d-path : {y₁ y₂ : ℝ} -> distance (- y₁) (- y₂) == distance y₁ y₂
        d-path = cong abs (sym minus-distrib-plus) >=> abs-minus

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isLocallyUniformlyContinuous-minus :
      {f : D -> ℝ} ->
      isLocallyUniformlyContinuous f ->
      isLocallyUniformlyContinuous (\x -> - (f x))
    isLocallyUniformlyContinuous-minus {f} lcf x =
      ∥-map (\ (δ , uc) -> (δ , isUniformlyContinuous-minus uc)) (lcf x)


module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isUniformlyContinuous-+ :
      {f g : D -> ℝ} ->
      isUniformlyContinuous f -> isUniformlyContinuous g ->
      isUniformlyContinuous (\x -> f x + g x)
    isUniformlyContinuous-+ {f} {g}
      (isUniformlyContinuous-cons cf) (isUniformlyContinuous-cons cg)
      .isUniformlyContinuous.close ε⁺@(ε , 0<ε) =
      ∥-map2 handle (cf ε/2⁺) (cg ε/2⁺)
      where
      ε/2⁺ : ℝ⁺
      ε/2⁺ = ε * 1/2 , *-preserves-0< 0<ε 0<1/2

      handle :
        Σ[ δ₁ ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δ₁ x₁ x₂ -> εClose ε/2⁺ (f x₁) (f x₂)) ->
        Σ[ δ₂ ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δ₂ x₁ x₂ -> εClose ε/2⁺ (g x₁) (g x₂)) ->
        Σ[ δ₃ ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δ₃ x₁ x₂ -> εClose ε⁺ (f x₁ + g x₁) (f x₂ + g x₂))
      handle ((d₁ , 0<d₁) , f-close) ((d₂ , 0<d₂) , g-close) =
        (min d₁ d₂ , min-greatest-< 0<d₁ 0<d₂) ,
        \x₁ x₂ x₁x₂<d ->
          trans-≤-<
            distance-+-swap
            (trans-<-=
              (+-preserves-< (f-close x₁ x₂ (trans-<-≤ x₁x₂<d min-≤-left))
                             (g-close x₁ x₂ (trans-<-≤ x₁x₂<d min-≤-right)))
              +-/2-path)

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isLocallyUniformlyContinuous-+ :
      {f g : D -> ℝ} ->
      isLocallyUniformlyContinuous f -> isLocallyUniformlyContinuous g ->
      isLocallyUniformlyContinuous (\x -> f x + g x)
    isLocallyUniformlyContinuous-+ {f} {g} lcf lcg x =
      ∥-map2 handle (lcf x) (lcg x)
      where
      fg : D -> ℝ
      fg x = f x + g x

      handle :
        Σ[ δ₁ ∈ ℝ⁺ ] (isUniformlyContinuous (restrict f (εBallAtS δ₁ x))) ->
        Σ[ δ₂ ∈ ℝ⁺ ] (isUniformlyContinuous (restrict g (εBallAtS δ₂ x))) ->
        Σ[ δ₃ ∈ ℝ⁺ ] (isUniformlyContinuous (restrict fg (εBallAtS δ₃ x)))
      handle (δ₁@(d₁ , 0<d₁) , ucf) (δ₂@(d₂ , 0<d₂) , ucg) =
        δ₃ , isUniformlyContinuous-+ uc-f'₃ uc-g'₃
        where

        δ₃ : ℝ⁺
        δ₃ = (min d₁ d₂ , min-greatest-< 0<d₁ 0<d₂)
        f'₃ : (εBallAt δ₃ x) -> ℝ
        f'₃ = restrict f _
        g'₃ : (εBallAt δ₃ x) -> ℝ
        g'₃ = restrict g _

        uc-f'₃ : isUniformlyContinuous f'₃
        uc-f'₃ = isUniformlyContinuous-⊆ ucf (\x c -> trans-<-≤ c min-≤-left)
        uc-g'₃ : isUniformlyContinuous g'₃
        uc-g'₃ = isUniformlyContinuous-⊆ ucg (\x c -> trans-<-≤ c min-≤-right)


module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    private
      isUniformlyContinuous-finMergeDep :
        ∀ (m : ℕ) (f : Fin m -> D -> ℝ) (fc : ∀ i -> isUniformlyContinuous (f i)) ->
        isUniformlyContinuous (\x -> finMergeDep (CommMonoid-+ ℝ) m (\i -> f i x))
      isUniformlyContinuous-finMergeDep 0 f fc =
        isUniformlyContinuous-const 0#
      isUniformlyContinuous-finMergeDep (suc m) f fc =
        isUniformlyContinuous-+ (fc zero-fin)
          (isUniformlyContinuous-finMergeDep m (f ∘ suc-fin) (fc ∘ suc-fin))

      isLocallyUniformlyContinuous-finMergeDep :
        ∀ (m : ℕ) (f : Fin m -> D -> ℝ) (fc : ∀ i -> isLocallyUniformlyContinuous (f i)) ->
        isLocallyUniformlyContinuous (\x -> finMergeDep (CommMonoid-+ ℝ) m (\i -> f i x))
      isLocallyUniformlyContinuous-finMergeDep 0 f fc =
        isLocallyUniformlyContinuous-const 0#
      isLocallyUniformlyContinuous-finMergeDep (suc m) f fc =
        isLocallyUniformlyContinuous-+ (fc zero-fin)
          (isLocallyUniformlyContinuous-finMergeDep m (f ∘ suc-fin) (fc ∘ suc-fin))


    isUniformlyContinuous-finiteSum : {ℓI : Level} {FI@(I , _) : FinSet ℓI}
      {f : I -> D -> ℝ} -> (∀ i -> isUniformlyContinuous (f i)) ->
      isUniformlyContinuous (\x -> finiteSumᵉ FI (\i -> f i x))
    isUniformlyContinuous-finiteSum {FI = FI@(I , isFin-I)} {f} fc =
      unsquash isProp-isUniformlyContinuous (∥-map handle isFin-I)
      where
      handle :
        Σ[ n ∈ ℕ ] (I ≃ Fin n) ->
        isUniformlyContinuous (\x -> finiteSumᵉ FI (\i -> f i x))
      handle (n , eq) =
        subst isUniformlyContinuous (funExt (\x -> sym (finiteMerge-eval eq)))
          (isUniformlyContinuous-finMergeDep n
            (\i x -> f (eqInv eq i) x)
            (\i -> fc (eqInv eq i)))

    isLocallyUniformlyContinuous-finiteSum : {ℓI : Level} {FI@(I , _) : FinSet ℓI}
      {f : I -> D -> ℝ} -> (∀ i -> isLocallyUniformlyContinuous (f i)) ->
      isLocallyUniformlyContinuous (\x -> finiteSumᵉ FI (\i -> f i x))
    isLocallyUniformlyContinuous-finiteSum {FI = FI@(I , isFin-I)} {f} fc =
      unsquash isProp-isLocallyUniformlyContinuous (∥-map handle isFin-I)
      where
      handle :
        Σ[ n ∈ ℕ ] (I ≃ Fin n) ->
        isLocallyUniformlyContinuous (\x -> finiteSumᵉ FI (\i -> f i x))
      handle (n , eq) =
        subst isLocallyUniformlyContinuous (funExt (\x -> sym (finiteMerge-eval eq)))
          (isLocallyUniformlyContinuous-finMergeDep n
            (\i x -> f (eqInv eq i) x)
            (\i -> fc (eqInv eq i)))
