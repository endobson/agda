{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.continuous where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import hlevel
open import metric-space
open import metric-space.instances.subspace
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import real.order
open import real.rational
open import real.subspace
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace
open import truncation

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where
  isContinuousAt : (A -> B) -> A -> Type _
  isContinuousAt f a =
    ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ] (∀ (a2 : A) -> εClose δ a a2 -> εClose ε (f a) (f a2))

  record isContinuous (f : A -> B) : Type (ℓ-max ℓA ℓ-one) where
    constructor isContinuous-cons
    field
      at : ∀ a -> isContinuousAt f a

  isProp-isContinuousAt : (f : A -> B) {a : A} -> isProp (isContinuousAt f a)
  isProp-isContinuousAt _ = isPropΠ (\_ -> squash)

  isProp-isContinuous : {f : A -> B} -> isProp (isContinuous f)
  isProp-isContinuous (isContinuous-cons c1) (isContinuous-cons c2) =
    cong isContinuous-cons (isPropΠ2 (\_ _ -> squash) c1 c2)

  isContinuousℚAt : (A -> B) -> A -> Type _
  isContinuousℚAt f a =
    ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℚ⁺ ] (∀ (a2 : A) -> εℚClose δ a a2 -> εClose ε (f a) (f a2))

  record isContinuousℚ (f : A -> B) : Type (ℓ-max ℓA ℓ-one) where
    constructor isContinuousℚ-cons
    field
      at : ∀ a -> isContinuousℚAt f a

  opaque
    isContinuous->isContinuousℚ : {f : A -> B} -> isContinuous f -> isContinuousℚ f
    isContinuous->isContinuousℚ {f} (isContinuous-cons c) .isContinuousℚ.at x ε =
      ∥-bind handle (c x ε)
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ (y : A) -> εClose δ x y -> εClose ε (f x) (f y)) ->
               ∃[ δ ∈ ℚ⁺ ] (∀ (y : A) -> εℚClose δ x y -> εClose ε (f x) (f y))
      handle ((δ1 , 0<δ1) , δ1-close) = ∥-map handle2 0<δ1
        where
        handle2 : 0# ℝ<' δ1 ->
                  Σ[ δ ∈ ℚ⁺ ] (∀ (y : A) -> εℚClose δ x y -> εClose ε (f x) (f y))
        handle2 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) = δ2⁺ , δ2-close
          where
          δ2⁺ : ℚ⁺
          δ2⁺ = δ2 , U->ℚ< 0U-δ2
          δ2-close : ∀ (y : A) -> εℚClose δ2⁺ x y -> εClose ε (f x) (f y)
          δ2-close y d<δ2 = δ1-close y (trans-< d<δ2 (L->ℝ< δ1L-δ2))


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}} where
  opaque
    isContinuous-const : ∀ (b : B) -> isContinuous (\(_ : A) -> b)
    isContinuous-const b .isContinuous.at a (ε , 0<ε) = ∣ (1# , 0<1) , close ∣
      where
      close : (a2 : A) -> distance a a2 < 1# -> distance b b < ε
      close _ _ = trans-=-< (path->zero-distance (reflᵉ b)) 0<ε

module _ {ℓA : Level} {A : Type ℓA} {{MS-A : MetricSpaceStr A}} where
  opaque
    isContinuous-id : isContinuous (\(a : A) -> a)
    isContinuous-id .isContinuous.at a (ε , 0<ε) = ∣ (ε , 0<ε) , close ∣
      where
      close : (a2 : A) -> distance a a2 < ε -> distance a a2 < ε
      close _ d<ε = d<ε

module _ {ℓD ℓS : Level} {D : Type ℓD} {{MS-D : MetricSpaceStr D}}
         {S : Subtype D ℓS} where
  opaque
    isContinuous-embed : isContinuous (\((x , _) : Subspace S) -> x)
    isContinuous-embed .isContinuous.at x∈@(x , _) (ε , 0<ε) = ∣ (ε , 0<ε) , close ∣
      where
      close : (y∈@(y , _) : Subspace S) -> distance x y < ε -> distance x y < ε
      close _ d<ε = d<ε


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {{MS-C : MetricSpaceStr C}}
         where
  opaque
    isContinuousAt-∘ :
      (g : B -> C) -> (f : A -> B) {a : A} ->
      isContinuousAt g (f a) -> isContinuousAt f a -> isContinuousAt (g ∘ f) a
    isContinuousAt-∘ g f {a} cg cf ε = (∥-bind handle (cg ε))
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ b -> εClose δ (f a) b -> εClose ε (g (f a)) (g b)) ->
               ∃[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose ε (g (f a)) (g (f a2)))
      handle (δ , δ-close) = ∥-map handle2 (cf δ)
        where
        handle2 : Σ[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose δ (f a) (f a2)) ->
                  Σ[ γ ∈ ℝ⁺ ] (∀ a2 -> εClose γ a a2 -> εClose ε (g (f a)) (g (f a2)))
        handle2 (γ , γ-close) = (γ , \a2 -> δ-close (f a2) ∘ (γ-close a2))


    isContinuous-∘ :
      {g : B -> C} -> {f : A -> B} ->
      isContinuous g -> isContinuous f -> isContinuous (g ∘ f)
    isContinuous-∘ {g} {f} (isContinuous-cons cg) (isContinuous-cons cf)
        .isContinuous.at a = isContinuousAt-∘ g f (cg (f a)) (cf a)
