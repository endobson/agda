{-# OPTIONS --cubical --safe --exact-split #-}

module category2.morphism.mono where

open import category2.base
open import category2.morphism.subcategory
open import base
open import isomorphism
open import equality-path
open import hlevel.base
open import hlevel.pi


module _ {ℓO ℓM : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         {{C : CategoryStr M}} where

  isMono : {o₁ o₂ : O} (f : M o₁ o₂) -> Type (ℓ-max ℓO ℓM)
  isMono {o₁} {o₂} f =
    ∀ {o₃ : O} {g₁ g₂ : M o₃ o₁} -> g₁ ⋆ f == g₂ ⋆ f -> g₁ == g₂

  opaque
    isSubCategory-isMono : isSubCategory isMono
    isSubCategory-isMono = record
      { isProp-S = isPropΠⁱ3 \_ _ _ -> isPropΠ \_ -> isSet-Mor _ _
      ; ⋆-closed = \m₁ m₂ p -> m₁ (m₂ (⋆-assoc ∙∙ p ∙∙ sym ⋆-assoc))
      ; S-id = \_ p -> sym ⋆-right-id ∙∙ p ∙∙ ⋆-right-id
      }

module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) where
  private
    module C = Category C
    instance
      CS = C.Str

  record Mono (o₁ o₂ : Obj C) : Type (ℓ-max ℓO ℓM) where
    constructor mono
    field
      f : C →[ o₁ , o₂ ]
      m : isMono f

  isΣSubCategory-Mono : isΣSubCategory C Mono
  isΣSubCategory-Mono = record
    { S = isMono
    ; isSub = isSubCategory-isMono
    ; eq = \_ _ -> isoToEquiv (iso
      (\{(mono f m) -> f , m})
      (\{(f , m) -> mono f m})
      (\_ -> refl)
      (\_ -> refl))
    }

module _ {ℓO ℓM : Level} {C : Category ℓO ℓM} where
  instance
    MonoCStr : CategoryStr (Mono C)
    MonoCStr = CategoryStr-ΣSub (isΣSubCategory-Mono C)
