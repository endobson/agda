{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.functor where

open import base
open import category.base
open import category.constructions.product
open import category.functor
open import category.natural-transformation
open import category.monoidal.base


module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD}
         (MC : MonoidalStr C) (MD : MonoidalStr D) where
  private
    module MC = MonoidalStrHelpers MC
    module MD = MonoidalStrHelpers MD

  record isMonoidalFunctor (F : Functor C D) : Type (ℓ-max* 4 ℓOC ℓMC ℓOD ℓMD) where
    field
      φ : NaturalTransformation ((product-functor F F) ⋆F MD.⊗) (MC.⊗ ⋆F F)
      φ-id : D [ MD.unit , F-obj F MC.unit ]

      α⇒ : {A B C : Obj C} ->
           (MD.α⇒ ⋆⟨ D ⟩ (id D MD.⊗₁ (NT-obj φ (B , C))) ⋆⟨ D ⟩ (NT-obj φ (A , (B MC.⊗₀ C))))
           ==
           ((NT-obj φ (A , B) MD.⊗₁ id D) ⋆⟨ D ⟩
            (NT-obj φ ((A MC.⊗₀ B) , C)) ⋆⟨ D ⟩
            (F-mor F MC.α⇒))

      λ⇒ : {A : Obj C} ->
           MD.λ⇒ ==
           ((φ-id MD.⊗₁ id D) ⋆⟨ D ⟩
            (NT-obj φ (MC.unit , A)) ⋆⟨ D ⟩
            (F-mor F MC.λ⇒))

      ρ⇒ : {A : Obj C} ->
           MD.ρ⇒ ==
           ((id D MD.⊗₁ φ-id) ⋆⟨ D ⟩
            (NT-obj φ (A , MC.unit)) ⋆⟨ D ⟩
            (F-mor F MC.ρ⇒))
