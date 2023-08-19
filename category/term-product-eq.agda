{-# OPTIONS --cubical --safe --exact-split #-}

module category.term-product-eq where

open import base
open import category.adjunction
open import category.base
open import category.constructions.functor-cat
open import category.constructions.product
open import category.functor
open import category.instances.terminal
open import category.natural-isomorphism
open import category.natural-transformation
open import equality


module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where

  private
    TC : PreCategory ℓO ℓM
    TC = ProductCat TermC C

    forward-F : Functor TC C
    forward-F = record
      { obj = \(tt , o) -> o
      ; mor = \(tt , m) -> m
      ; id = \_ -> refl
      ; ⋆ = \_ _ -> refl
      }

    backward-F : Functor C TC
    backward-F = record
      { obj = \o -> tt , o
      ; mor = \m -> tt , m
      ; id = \_ -> refl
      ; ⋆ = \_ _ -> refl
      }

    unit : NaturalTransformation (idF TC) (forward-F ⋆F backward-F)
    unit = record
      { obj = \c -> id TC
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
      where
      open CategoryHelpers TC

    counit : NaturalTransformation (backward-F ⋆F forward-F) (idF C)
    counit = record
      { obj = \c -> id C
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
      where
      open CategoryHelpers C

    isIso-unit : isNaturalIso _ _ unit
    isIso-unit _ = record
      { inv = id TC
      ; ret = ⋆-id²
      ; sec = ⋆-id²
      }
      where
      open CategoryHelpers TC

    isIso-counit : isNaturalIso _ _ counit
    isIso-counit _ = record
      { inv = id C
      ; ret = ⋆-id²
      ; sec = ⋆-id²
      }
      where
      open CategoryHelpers C

  TermProduct-Adj : Adjunction forward-F backward-F
  TermProduct-Adj = record
    { unit = unit
    ; counit = counit
    ; tri-L = \_ -> PreCategory.⋆-id² C
    ; tri-R = \_ -> PreCategory.⋆-id² TC
    }

  TermProduct-AdjEq : AdjointEquiv forward-F backward-F
  TermProduct-AdjEq = TermProduct-Adj , (isIso-unit , isIso-counit)
