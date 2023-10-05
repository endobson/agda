{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.functor-cat where

open import base
open import category.base
open import category.functor
open import category.natural-transformation
open import cubical
open import equality-path
open import funext
open import hlevel

module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
         (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) where
  private
    module C = PreCategory C
    module D = PreCategory D
    ℓF = (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD)

  FunctorC : PreCategory ℓF ℓF
  FunctorC .PreCategory.Obj = Functor C D
  FunctorC .PreCategory.Mor = NaturalTransformation
  FunctorC .PreCategory.id = id-NT _
  FunctorC .PreCategory._⋆_ = _⋆NT_
  FunctorC .PreCategory.⋆-left-id = ⋆NT-left-id
  FunctorC .PreCategory.⋆-right-id = ⋆NT-right-id
  FunctorC .PreCategory.⋆-assoc = ⋆NT-assoc
  FunctorC .PreCategory.isSet-Mor = isSet-NaturalTransformation

  diagonal-functor : Functor D FunctorC
  diagonal-functor = record
    { obj = \d -> constantF C D d
    ; mor = \f -> record
      { obj = \_ -> f
      ; mor = \_ -> D.⋆-right-id _ >=> sym (D.⋆-left-id _)
      }
    ; id = \_ -> natural-transformation-path (\_ -> refl)
    ; ⋆ = \_ _ -> natural-transformation-path (\_ -> refl)
    }
