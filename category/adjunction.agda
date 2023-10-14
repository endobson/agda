{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.functor
open import category.natural-transformation
open import category.natural-isomorphism

module category.adjunction where

module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD} where

  record Adjunction (L : Functor C D) (R : Functor D C) : Type (ℓ-max* 4 ℓOC ℓMC ℓOD ℓMD) where
    field
      unit : NaturalTransformation (idF C) (L ⋆F R)
      counit : NaturalTransformation (R ⋆F L) (idF D)

      tri-L : ∀ (c : Obj C) -> (NT-obj (unit NT▶ L) c) ⋆⟨ D ⟩ (NT-obj (L NT◀ counit) c) == id D
      tri-R : ∀ (d : Obj D) -> (NT-obj (R NT◀ unit) d) ⋆⟨ C ⟩ (NT-obj (counit NT▶ R) d) == id C

    module unit = NaturalTransformation unit
    module counit = NaturalTransformation counit

  AdjointEquiv : (L : Functor C D) (R : Functor D C) -> Type _
  AdjointEquiv L R = Σ (Adjunction L R) AdjunctionEquiv
    where
    AdjunctionEquiv : Adjunction L R -> Type _
    AdjunctionEquiv adj = isNaturalIso _ _ unit × isNaturalIso _ _ counit
      where
      open Adjunction adj

  isEquivC : (Functor C D) -> Type _
  isEquivC L = Σ[ R ∈ Functor D C ] (AdjointEquiv L R)

_≃C_ : {ℓOC ℓMC ℓOD ℓMD : Level} -> (PreCategory ℓOC ℓMC) -> (PreCategory ℓOD ℓMD) -> Type _
C ≃C D = Σ (Functor C D) isEquivC
