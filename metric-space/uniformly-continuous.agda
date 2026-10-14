{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.uniformly-continuous where

open import additive-group.instances.real
open import base
open import equality-path
open import functions
open import hlevel.base
open import metric-space
open import metric-space.instances.subspace
open import metric-space.ball-subspace
open import order
open import order.minmax
open import order.minmax.instances.real
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import real.subspace
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace
open import truncation
open import funext


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where

  record isUniformlyContinuous (f : A -> B) : Type (ℓ-max ℓA ℓ-one) where
    constructor isUniformlyContinuous-cons
    field
      close : ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ] ∀ a₁ a₂ -> εClose δ a₁ a₂ -> εClose ε (f a₁) (f a₂)


  isProp-isUniformlyContinuous : {f : A -> B} -> isProp (isUniformlyContinuous f)
  isProp-isUniformlyContinuous
    (isUniformlyContinuous-cons c₁) (isUniformlyContinuous-cons c₂) =
    cong isUniformlyContinuous-cons (isPropΠ (\_ -> squash) c₁ c₂)




module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}} where
  opaque
    isUniformlyContinuous-const : ∀ (b : B) -> isUniformlyContinuous (\(_ : A) -> b)
    isUniformlyContinuous-const b .isUniformlyContinuous.close (ε , 0<ε) = ∣ (1# , 0<1) , close ∣
      where
      close : (a₁ a₂ : A) -> distance a₁ a₂ < 1# -> distance b b < ε
      close _ _ _ = trans-=-< (path->zero-distance (reflᵉ b)) 0<ε

module _ {ℓA : Level} {A : Type ℓA} {{MS-A : MetricSpaceStr A}} where
  opaque
    isUniformlyContinuous-id : isUniformlyContinuous (\(a : A) -> a)
    isUniformlyContinuous-id .isUniformlyContinuous.close (ε , 0<ε) = ∣ (ε , 0<ε) , close ∣
      where
      close : (a₁ a₂ : A) -> distance a₁ a₂ < ε -> distance a₁ a₂ < ε
      close _ _ d<ε = d<ε

module _ {ℓD ℓS : Level} {D : Type ℓD} {{MS-D : MetricSpaceStr D}}
         {S : Subtype D ℓS} where
  opaque
    isUniformlyContinuous-embed : isUniformlyContinuous (\((x , _) : Subspace S) -> x)
    isUniformlyContinuous-embed .isUniformlyContinuous.close (ε , 0<ε) = ∣ (ε , 0<ε) , close ∣
      where
      close : (x∈@(x , _) y∈@(y , _) : Subspace S) -> distance x y < ε -> distance x y < ε
      close _ _ d<ε = d<ε

module _ {ℓD ℓS₁ ℓS₂ ℓA : Level} {D : Type ℓD} {A : Type ℓA}
         {{MS-D : MetricSpaceStr D}}
         {{MS-A : MetricSpaceStr A}}
         {S₁ : Subtype D ℓS₁} {S₂ : Subtype D ℓS₂}
         where
  opaque
    isUniformlyContinuous-⊆ :
      {f : Subspace S₂ -> A} ->
      isUniformlyContinuous f ->
      (inc : ∀ x -> ⟨ S₁ x ⟩ -> ⟨ S₂ x ⟩) ->
      isUniformlyContinuous (\((x , p) : Subspace S₁) -> f (x , inc x p))
    isUniformlyContinuous-⊆ {f} cf inc .isUniformlyContinuous.close ε =
      ∥-map handle (isUniformlyContinuous.close cf ε)
      where
      f' : Subspace S₁ -> A
      f' (x , p) = f (x , inc x p)

      handle : (Σ[ δ ∈ ℝ⁺ ] ∀ x₁ x₂ -> εClose δ x₁ x₂ -> εClose ε (f x₁) (f x₂)) ->
               (Σ[ δ ∈ ℝ⁺ ] ∀ x₁ x₂ -> εClose δ x₁ x₂ -> εClose ε (f' x₁) (f' x₂))
      handle (δ , f-close) = (δ , \ (x₁ , p₁) (x₂ , p₂) c -> f-close (x₁ , inc x₁ p₁) (x₂ , inc x₂ p₂) c)

module _
  {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}} {{MS-C : MetricSpaceStr C}}
  where
  opaque
    isUniformlyContinuous-∘ :
      {g : B -> C} {f : A -> B} ->
      isUniformlyContinuous g -> isUniformlyContinuous f -> isUniformlyContinuous (g ∘ f)
    isUniformlyContinuous-∘ {g} {f}
      (isUniformlyContinuous-cons cg) (isUniformlyContinuous-cons cf)
      .isUniformlyContinuous.close ε = (∥-bind handle (cg ε))
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ b₁ b₂ -> εClose δ b₁ b₂ -> εClose ε (g b₁) (g b₂)) ->
               ∃[ γ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose γ a₁ a₂ -> εClose ε (g (f a₁)) (g (f a₂)))
      handle (δ , δ-close) = ∥-map handle2 (cf δ)
        where
        handle2 : Σ[ γ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose γ a₁ a₂ -> εClose δ (f a₁) (f a₂)) ->
                  Σ[ γ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose γ a₁ a₂ -> εClose ε (g (f a₁)) (g (f a₂)))
        handle2 (γ , γ-close) = (γ , \a₁ a₂ -> δ-close (f a₁) (f a₂) ∘ (γ-close a₁ a₂))




module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where

  isLocallyUniformlyContinuous : Pred (A -> B) (ℓ-max ℓA ℓ-one)
  isLocallyUniformlyContinuous f =
    ∀ a₀ -> ∃[ δ₀ ∈ ℝ⁺ ] (isUniformlyContinuous (restrict f (εBallAtS δ₀ a₀)))


  isProp-isLocallyUniformlyContinuous : {f : A -> B} -> isProp (isLocallyUniformlyContinuous f)
  isProp-isLocallyUniformlyContinuous =
    isPropΠ (\_ -> squash)



module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}} where
  opaque
    isLocallyUniformlyContinuous-const : ∀ (b : B) -> isLocallyUniformlyContinuous (\(_ : A) -> b)
    isLocallyUniformlyContinuous-const b a = ∣ (1# , 0<1) , isUniformlyContinuous-const b ∣

module _ {ℓA : Level} {A : Type ℓA} {{MS-A : MetricSpaceStr A}} where
  opaque
    isLocallyUniformlyContinuous-id : isLocallyUniformlyContinuous (\(a : A) -> a)
    isLocallyUniformlyContinuous-id a = ∣ (1# , 0<1) , isUniformlyContinuous-embed ∣

module _ {ℓD ℓS : Level} {D : Type ℓD} {{MS-D : MetricSpaceStr D}}
         {S : Subtype D ℓS} where
  opaque
    isLocallyUniformlyContinuous-embed : isLocallyUniformlyContinuous (\((x , _) : Subspace S) -> x)
    isLocallyUniformlyContinuous-embed a =
      ∣ (1# , 0<1) ,
        isUniformlyContinuous-∘ isUniformlyContinuous-embed isUniformlyContinuous-embed ∣


module _
  {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}} {{MS-C : MetricSpaceStr C}}
  where
  opaque
    isLocallyUniformlyContinuous-∘ :
      {g : B -> C} {f : A -> B} ->
      isLocallyUniformlyContinuous g -> isLocallyUniformlyContinuous f ->
      isLocallyUniformlyContinuous (g ∘ f)
    isLocallyUniformlyContinuous-∘ {g} {f} lcg lcf a = ∥-bind2 handle (lcg (f a)) (lcf a)
      where
      g' : (δ : ℝ⁺) -> εBallAt δ (f a) -> C
      g' _ = restrict g _
      f' : (δ : ℝ⁺) -> εBallAt δ a -> B
      f' _ = restrict f _
      gf' : (δ : ℝ⁺) -> εBallAt δ a -> C
      gf' _ = restrict (g ∘ f) _

      handle :
        Σ[ δ₁ ∈ ℝ⁺ ] (isUniformlyContinuous (g' δ₁)) ->
        Σ[ δ₂ ∈ ℝ⁺ ] (isUniformlyContinuous (f' δ₂)) ->
        ∃[ δ ∈ ℝ⁺ ] (isUniformlyContinuous (gf' δ))
      handle (δ₁@(d₁ , 0<d₁) , ucg') (δ₂@(d₂ , 0<d₂) , ucf') =
        ∥-bind handle2 (isUniformlyContinuous.close ucf' δ₁)
        where
        handle2 :
          Σ[ δ₃ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose δ₃ a₁ a₂ -> εClose δ₁ (f' δ₂ a₁) (f' δ₂ a₂)) ->
          ∃[ δ ∈ ℝ⁺ ] (isUniformlyContinuous (gf' δ))
        handle2 (δ₃@(d₃ , 0<d₃) , f'-δ₁-close) = ∣ δ₄ , isUniformlyContinuous-∘ ucg' ucf'₂ ∣
          where
          δ₄ : ℝ⁺
          δ₄ = min d₂ d₃ , min-greatest-< 0<d₂ 0<d₃

          f'₂ : εBallAt δ₄ a -> εBallAt δ₁ (f a)
          f'₂ (a' , aa'<d₄) = f a' , f'-δ₁-close (a  , trans-=-< (path->zero-distance (reflᵉ a)) 0<d₂)
                                                 (a' , (trans-<-≤ aa'<d₄ min-≤-left))
                                                 (trans-<-≤ aa'<d₄ min-≤-right)

          ucf'₂ : isUniformlyContinuous f'₂
          ucf'₂ .isUniformlyContinuous.close ε =
            ∥-bind handle3 (isUniformlyContinuous.close ucf' ε)
            where
            handle3 :
              Σ[ δ₅ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose δ₅ a₁ a₂ -> εClose ε (f' δ₂ a₁) (f' δ₂ a₂)) ->
              ∃[ δ₅ ∈ ℝ⁺ ] (∀ a₁ a₂ -> εClose δ₅ a₁ a₂ -> εClose ε (f'₂ a₁) (f'₂ a₂))
            handle3 (δ₅ , f'-ε-close) = ∣ δ₅ , f'₂-close ∣

              where
              f'₂-close : ∀ a₁ a₂ -> εClose δ₅ a₁ a₂ -> εClose ε (f'₂ a₁) (f'₂ a₂)
              f'₂-close (a₁ , aa₁<δ₄) (a₂ , aa₂<δ₄) a₁a₂<d₅ =
                f'-ε-close (a₁ , (trans-<-≤ aa₁<δ₄ min-≤-left))
                           (a₂ , (trans-<-≤ aa₂<δ₄ min-≤-left))
                           a₁a₂<d₅
