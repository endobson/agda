{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.cauchy where

open import base
open import additive-group.instances.real
open import metric-space
open import metric-space.ball-subspace
open import order
open import hlevel.base
open import order.instances.nat
open import order.instances.real
open import real.subspace
open import semiring
open import ordered-semiring
open import sequence
open import ring.implementations.real
open import ordered-semiring.instances.real
open import subset.subspace
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {{MS : MetricSpaceStr D}} where
  isCauchy : Sequence D -> Type ℓ-one
  isCauchy s =
    ∀ (ε : ℝ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂))

  isCauchy' : Sequence D -> Type ℓ-one
  isCauchy' s =
    ∀ (ε : ℝ⁺) -> ∀Largeℕ (\n -> (m : Nat) -> n ≤ m -> εClose ε (s n) (s m))

  opaque
    isCauchy->isCauchy' : {s : Sequence D} -> isCauchy s -> isCauchy' s
    isCauchy->isCauchy' cauchy ε =
      ∥-map (\ (n , f) -> n , \m₁ n≤m₁ m₂ m₁≤m₂ -> f m₁ m₂ n≤m₁ (trans-≤ n≤m₁ m₁≤m₂)) (cauchy ε)

    isCauchy'->isCauchy : {s : Sequence D} -> isCauchy' s -> isCauchy s
    isCauchy'->isCauchy {s} cauchy' ε = ∥-map handle (cauchy' ε)
      where
      handle : ∀Largeℕ' (\n -> (m : Nat) -> n ≤ m -> εClose ε (s n) (s m)) ->
               Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂))
      handle (n , f) = n , (\m₁ m₂ -> g m₁ m₂ (split-< m₁ m₂))
        where
        g : (m₁ m₂ : Nat) -> (m₁ < m₂ ⊎ m₂ ≤ m₁) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂)
        g m₁ m₂ (inj-l m₁<m₂) n≤m₁ n≤m₂ = f m₁ n≤m₁ m₂ (weaken-< m₁<m₂)
        g m₁ m₂ (inj-r m₂≤m₁) n≤m₁ n≤m₂ = trans-=-< distance-commute (f m₂ n≤m₂ m₁ m₂≤m₁)

  isProp-isCauchy : (s : Sequence D) -> isProp (isCauchy s)
  isProp-isCauchy _ = isPropΠ (\_ -> squash)


module _ {ℓA ℓD : Level} {A : Type ℓA} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  isUniformlyCauchy : Sequence (A -> D) -> Type (ℓ-max ℓ-one ℓA)
  isUniformlyCauchy s =
    ∀ (ε : ℝ⁺) -> ∃[ n ∈ Nat ] ((a : A) (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁ a) (s m₂ a))


module _ {ℓA ℓD : Level} {A : Type ℓA} {D : Type ℓD}
         {{MS-A : MetricSpaceStr A}} {{MS-D : MetricSpaceStr D}} where

  isLocallyUniformlyCauchy : Sequence (A -> D) -> Type (ℓ-max ℓ-one ℓA)
  isLocallyUniformlyCauchy s =
    ∀ (a : A) -> ∃[ δ ∈ ℝ⁺ ] isUniformlyCauchy (\n -> restrict (s n) (εBallAtS δ a))


module _ {ℓA ℓD : Level} {A : Type ℓA} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isUniformlyCauchy->isCauchy :
      {s : Sequence (A -> D)} -> isUniformlyCauchy s -> ∀ a -> isCauchy (\i -> s i a)
    isUniformlyCauchy->isCauchy uc a ε = ∥-map (\ (n , f) -> n , f a) (uc ε)



module _ {ℓA ℓD : Level} {A : Type ℓA} {D : Type ℓD}
         {{MS-A : MetricSpaceStr A}} {{MS-D : MetricSpaceStr D}} where

  opaque
    isUniformlyCauchy->isLocallyUniformlyCauchy :
      {s : Sequence (A -> D)} -> isUniformlyCauchy s -> isLocallyUniformlyCauchy s
    isUniformlyCauchy->isLocallyUniformlyCauchy {s} uc a = ∣ 1⁺ , isUniformlyCauchy-s' ∣
      where
      1⁺ : ℝ⁺
      1⁺ = 1# , 0<1

      s' : Sequence (εBallAt 1⁺ a -> D)
      s' n = restrict (s n) (εBallAtS 1⁺ a)

      isUniformlyCauchy-s' : isUniformlyCauchy s'
      isUniformlyCauchy-s' ε = ∥-map handle (uc ε)
        where
        handle :
          (Σ[ n ∈ Nat ] ((a' : A) (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁ a') (s m₂ a'))) ->
          (Σ[ n ∈ Nat ] ((a' : εBallAt 1⁺ a) (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s' m₁ a') (s' m₂ a')))
        handle (n , close) = n , (\ (a , _) -> close a)



    isLocallyUniformlyCauchy->isCauchy :
      {s : Sequence (A -> D)} -> isLocallyUniformlyCauchy s -> ∀ a -> isCauchy (\i -> s i a)
    isLocallyUniformlyCauchy->isCauchy {s} luc a =
      unsquash (isProp-isCauchy s') (∥-map handle (luc a))
      where
      s' : Sequence D
      s' i = s i a

      handle :
        (Σ[ δ ∈ ℝ⁺ ] isUniformlyCauchy (\n -> restrict (s n) (εBallAtS δ a))) ->
        isCauchy s'
      handle (δ⁺@(δ , 0<δ) , uc) =
        isUniformlyCauchy->isCauchy {s = (\n -> restrict (s n) (εBallAtS δ⁺ a))} uc a'
        where
        a' : εBallAt δ⁺ a
        a' = a , trans-=-< (path->zero-distance (reflᵉ a)) 0<δ
