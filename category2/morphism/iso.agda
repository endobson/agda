{-# OPTIONS --cubical --safe --exact-split #-}

module category2.morphism.iso where


open import category2.base
open import category2.morphism.subcategory
open import base
open import equality-path
open import hlevel.base
open import hlevel.pi

import isomorphism as i


module _ {ℓO ℓM : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         {{C : CategoryStr M}} where

  record isIso {o₁ o₂ : O} (f : M o₁ o₂) : Type (ℓ-max ℓO ℓM) where
    constructor is-iso
    field
      inv : M o₂ o₁
      rightInv : f ⋆ inv == idᵉ o₁
      leftInv : inv ⋆ f == idᵉ o₂

  module _ {o₁ o₂ : O} {f : M o₁ o₂} where
    opaque
      isProp-isIso : isProp (isIso f)
      isProp-isIso (is-iso inv₁ r₁ l₁) (is-iso inv₂ r₂ l₂) =
        \i -> is-iso (inv-path i) (r-path i) (l-path i)
        where
        inv-path : inv₁ == inv₂
        inv-path =
          sym ⋆-right-id >=>
          ⋆-right (sym r₂) >=>
          sym ⋆-assoc >=>
          ⋆-left l₁ >=>
          ⋆-left-id

        r-path : PathP (\i -> f ⋆ inv-path i == id) r₁ r₂
        r-path = isProp->PathP (\_ -> isSet-Mor _ _)
        l-path : PathP (\i -> inv-path i ⋆ f == id) l₁ l₂
        l-path = isProp->PathP (\_ -> isSet-Mor _ _)

  private
    module _ {o₁ o₂ o₃ : O} {f : M o₁ o₂} {g : M o₂ o₃}
      where

      ⋆-closed-isIso : (isIso f) -> (isIso g) -> isIso (f ⋆ g)
      ⋆-closed-isIso (is-iso i₁ r₁ l₁) (is-iso i₂ r₂ l₂) = record
        { inv = i₂ ⋆ i₁
        ; rightInv = rightInv
        ; leftInv = leftInv
        }
        where
        opaque
          rightInv : (f ⋆ g) ⋆ (i₂ ⋆ i₁) == id
          rightInv = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left r₂ >=> ⋆-left-id) >=> r₁
          leftInv : (i₂ ⋆ i₁) ⋆ (f ⋆ g) == id
          leftInv = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left l₁ >=> ⋆-left-id) >=> l₂

    isIso-id : ∀ (o : O) -> isIso (idᵉ o)
    isIso-id o = record
      { inv = idᵉ o
      ; rightInv = ⋆-right-id
      ; leftInv = ⋆-left-id
      }

  isSubCategory-isIso : isSubCategory isIso
  isSubCategory-isIso = record
    { isProp-S = isProp-isIso
    ; ⋆-closed = ⋆-closed-isIso
    ; S-id = isIso-id
    }


module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) where
  private
    module C = Category C
    instance
      CS = C.Str

  record Iso (o₁ o₂ : Obj C) : Type (ℓ-max ℓO ℓM) where
    constructor iso
    field
      f : C →[ o₁ , o₂ ]
      i : isIso f

    open isIso i public


  isΣSubCategory-Iso : isΣSubCategory C Iso
  isΣSubCategory-Iso = record
    { S = isIso
    ; isSub = isSubCategory-isIso
    ; eq = \_ _ -> i.isoToEquiv (i.iso
      (\{(iso f i) -> f , i})
      (\{(f , i) -> iso f i})
      (\_ -> refl)
      (\_ -> refl))
    }

module _ {ℓO ℓM : Level} {C : Category ℓO ℓM} where
  instance
    IsoCStr : CategoryStr (Iso C)
    IsoCStr = CategoryStr-ΣSub (isΣSubCategory-Iso C)
