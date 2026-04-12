{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.suspension-loop-eq where

open import base
open import cubical
open import equality-path
open import equivalence
open import functions
open import isomorphism
open import pointed.base
open import pointed.loop-space
open import pointed.suspension

module _ {ℓA ℓB : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) where

  private
    T₁ T₂ T₃ T₄ T₅ : Type (ℓ-max ℓA ℓB)
    T₁ = Susp∙ A∙ ->∙ B∙
    T₂ = Σ[ b₁ ∈ B ] Σ[ p₁ ∈ (b₁ == ★B) ]
         Σ[ b₂ ∈ B ] Σ[ p₂ ∈ b₁ == b₂ ]
         Σ[ f ∈ (A -> b₁ == b₂) ] (f ★A == p₂)
    T₃ = Σ[ b₂ ∈ B ] Σ[ p₂ ∈ ★B == b₂ ]
         Σ[ f ∈ (A -> ★B == b₂) ] (f ★A == p₂)
    T₄ = Σ[ f ∈ (A -> ★B == ★B) ] (f ★A == refl)
    T₅ = A∙ ->∙ Ω B∙

    iso₁ : Iso T₁ T₂
    iso₁ = iso forward backward fb bf
      where
      open _->∙_
      forward : T₁ -> T₂
      forward (->∙-cons f p) = (f north , p , f south , (\i -> f (meridian ★A i)) , (\a i -> f (meridian a i)) , refl)
      backward : T₂ -> T₁
      backward (b₁ , p , b₂ , _ , ps , _) .f north = b₁
      backward (b₁ , p , b₂ , _ , ps , _) .f south = b₂
      backward (b₁ , p , b₂ , _ , ps , _) .f (meridian a i) = ps a i
      backward (b₁ , p , b₂ , _ , ps , _) .preserves-★ = p

      fb : ∀ x -> forward (backward x) == x
      fb (b₁ , p , b₂ , p₂ , ps , p₃) i = b₁ , p , b₂ , p₃ i , ps , (\j -> p₃ (j ∧ i))
      bf : ∀ x -> backward (forward x) == x
      bf (->∙-cons f p) _ .f north = f north
      bf (->∙-cons f p) _ .f south = f south
      bf (->∙-cons f p) _ .f (meridian a i) = f (meridian a i)
      bf (->∙-cons f p) _ .preserves-★ = p


    iso₂ : Iso T₂ T₃
    iso₂ = singletonInduction₁-iso (\_ -> _)
    iso₃ : Iso T₃ T₄
    iso₃ = singletonInduction₂-iso (\_ -> _)

    iso₄ : Iso T₄ T₅
    iso₄ = iso (\ (ps , p) -> ->∙-cons ps p) (\ (->∙-cons ps p) -> ps , p)
               (\_ -> refl) (\_ -> refl)

    ★T₁ : T₁
    ★T₁ = const->∙
    ★T₂ : T₂
    ★T₂ = (★B , refl , ★B , refl , (\_ -> refl) , refl)
    ★T₃ : T₃
    ★T₃ = (★B , refl , (\_ -> refl) , refl)
    ★T₄ : T₄
    ★T₄ = (\_ -> refl) , refl
    ★T₅ : T₅
    ★T₅ = const->∙

    ★path₁₂ : Iso.fun iso₁ ★T₁ == ★T₂
    ★path₁₂ = refl
    ★path₂₃ : Iso.fun iso₂ ★T₂ == ★T₃
    ★path₂₃ = Iso.rightInv iso₂ _
    ★path₃₄ : Iso.fun iso₃ ★T₃ == ★T₄
    ★path₃₄ = Iso.rightInv iso₃ _
    ★path₄₅ : Iso.fun iso₄ ★T₄ == ★T₅
    ★path₄₅ = refl

    ★path : Iso.fun ((iso₁ >iso> iso₂) >iso> (iso₃ >iso> iso₄)) const->∙ == const->∙
    ★path =
      cong (Iso.fun iso₄ ∘ Iso.fun iso₃) ★path₂₃ >=>
      cong (Iso.fun iso₄) ★path₃₄


  Susp∙-Ω-map-eq : (Susp∙ A∙ ->∙ B∙) ≃ (A∙ ->∙ Ω B∙)
  Susp∙-Ω-map-eq = isoToEquiv ((iso₁ >iso> iso₂) >iso> (iso₃ >iso> iso₄))

  Susp∙-Ω-map-path : (Susp∙ A∙ ->∙∙ B∙) == (A∙ ->∙∙ Ω B∙)
  Susp∙-Ω-map-path = Type∙-path (Susp∙-Ω-map-eq , ★path)
