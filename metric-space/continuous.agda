{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.continuous where

open import base
open import functions
open import hlevel
open import metric-space
open import order
open import order.instances.real
open import ordered-additive-group.instances.real
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {{MS : MetricSpaceStr D}} where
  εClose : ℝ⁺ -> D -> D -> Type ℓ-one
  εClose (ε , _) x y = (distance x y) < ε

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where
  isContinuousAt : A -> (A -> B) -> Type _
  isContinuousAt a f =
    ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ] (∀ (a2 : A) -> εClose δ a a2 -> εClose ε (f a) (f a2))

  isContinuous : (A -> B) -> Type _
  isContinuous f = ∀ a -> isContinuousAt a f

  isProp-isContinuousAt : {a : A} {f : A -> B} -> isProp (isContinuousAt a f)
  isProp-isContinuousAt = isPropΠ (\_ -> squash)

  isProp-isContinuous : {f : A -> B} -> isProp (isContinuous f)
  isProp-isContinuous = isPropΠ2 (\_ _ -> squash)

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {{MS-C : MetricSpaceStr C}}
         where
  opaque
    ∘-isContinuous :
      {g : B -> C} -> {f : A -> B} ->
      isContinuous g -> isContinuous f -> isContinuous (g ∘ f)
    ∘-isContinuous {g} {f} cg cf a ε = ∥-bind handle (cg (f a) ε)
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ b -> εClose δ (f a) b -> εClose ε (g (f a)) (g b)) ->
               ∃[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose ε (g (f a)) (g (f a2)))
      handle (δ , δ-close) = ∥-map handle2 (cf a δ)
        where
        handle2 : Σ[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose δ (f a) (f a2)) ->
                  Σ[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose ε (g (f a)) (g (f a2)))
        handle2 (γ , γ-close) = (γ , \a2 -> δ-close (f a2) ∘ (γ-close a2))
