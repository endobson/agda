{-# OPTIONS --cubical --safe --exact-split #-}

module category2.morphism.subcategory where

open import base
open import category2.base
open import equality-path
open import equivalence
open import hlevel
open import hlevel.base
open import sigma.base


module _ {ℓO ℓM ℓS : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         {{C : CategoryStr M}}
         (S : {o₁ o₂ : O} (f : M o₁ o₂) -> Type ℓS)
         where
  record isSubCategory : Type (ℓ-max* 3 ℓO ℓM ℓS) where
    field
      isProp-S : {o₁ o₂ : O} {f : M o₁ o₂} -> isProp (S f)
      ⋆-closed : {o₁ o₂ o₃ : O} {f₁ : M o₁ o₂} {f₂ : M o₂ o₃} ->
                 S f₁ -> S f₂ -> S (f₁ ⋆ f₂)
      S-id : (o : O) -> S (idᵉ o)


module _ {ℓO ℓM ℓS : Level}
         (C : Category ℓO ℓM) (ΣS : Rel (Obj C) ℓS) where
  private
    module C = Category C
    instance
      CS = C.Str


  record isΣSubCategory : Type (ℓ-max* 3 ℓO ℓM (ℓ-suc ℓS)) where
    field
      S : {o₁ o₂ : Obj C} -> Pred (C →[ o₁ , o₂ ]) ℓS
      isSub : isSubCategory S
      eq : ∀ o₁ o₂ -> ΣS o₁ o₂ ≃ Σ (C →[ o₁ , o₂ ]) S


module _
  {ℓO ℓM ℓS : Level} {C : Category ℓO ℓM} {ΣS : Rel (Obj C) ℓS}
  (SC : isΣSubCategory C ΣS)
  where

  private
    module C = Category C
    module SC = isΣSubCategory SC
    instance
      CS = C.Str
    module Sub = isSubCategory SC.isSub

    Σ'S : Rel (Obj C) (ℓ-max ℓM ℓS)
    Σ'S o₁ o₂ = Σ (C →[ o₁ , o₂ ]) SC.S

    ⇒ : {o₁ o₂ : Obj C} -> ΣS o₁ o₂ -> Σ'S o₁ o₂
    ⇒ = eqFun (SC.eq _ _)
    ⇐ : {o₁ o₂ : Obj C} -> Σ'S o₁ o₂ -> ΣS o₁ o₂
    ⇐ = eqInv (SC.eq _ _)
    ⇐⇒ : {o₁ o₂ : Obj C} {f : ΣS o₁ o₂} -> ⇐ (⇒ f) == f
    ⇐⇒ = eqRet (SC.eq _ _) _
    ⇒⇐ : {o₁ o₂ : Obj C} {f : Σ'S o₁ o₂} -> ⇒ (⇐ f) == f
    ⇒⇐ = eqSec (SC.eq _ _) _

    Σ'id : {o : Obj C} -> Σ'S o o
    Σ'id = (id , Sub.S-id _)
    Σid : {o : Obj C} -> ΣS o o
    Σid = ⇐ Σ'id

    _Σ'⋆_ : {o₁ o₂ o₃ : Obj C} -> Σ'S o₁ o₂ -> Σ'S o₂ o₃ -> Σ'S o₁ o₃
    _Σ'⋆_ (f₁ , s₁) (f₂ , s₂) = f₁ ⋆ f₂ , Sub.⋆-closed s₁ s₂
    _Σ⋆_ : {o₁ o₂ o₃ : Obj C} -> ΣS o₁ o₂ -> ΣS o₂ o₃ -> ΣS o₁ o₃
    _Σ⋆_ f₁ f₂ = ⇐ ((⇒ f₁) Σ'⋆ (⇒ f₂))

    ⇒⋆ : {o₁ o₂ o₃ : Obj C} {f : ΣS o₁ o₂} {g : ΣS o₂ o₃} ->
         (⇒ (f Σ⋆ g)) == ((⇒ f) Σ'⋆ (⇒ g))
    ⇒⋆ = ⇒⇐

    ΣS-path : {o₁ o₂ : Obj C} {f₁ f₂ : ΣS o₁ o₂} -> ⟨ ⇒ f₁ ⟩ == ⟨ ⇒ f₂ ⟩ -> f₁ == f₂
    ΣS-path p = sym ⇐⇒ ∙∙ cong ⇐ (ΣProp-path Sub.isProp-S p) ∙∙ ⇐⇒

    opaque
      Σ⋆-left-idᵉ : {o₁ o₂ : Obj C} (f : ΣS o₁ o₂) -> Σid Σ⋆ f == f
      Σ⋆-left-idᵉ f = ΣS-path (cong fst (⇒⇐ >=> (cong (_Σ'⋆ (⇒ f)) ⇒⇐)) >=> ⋆-left-id)
      Σ⋆-right-idᵉ : {o₁ o₂ : Obj C} (f : ΣS o₁ o₂) -> f Σ⋆ Σid == f
      Σ⋆-right-idᵉ f = ΣS-path (cong fst (⇒⇐ >=> (cong ((⇒ f) Σ'⋆_) ⇒⇐)) >=> ⋆-right-id)


      Σ⋆-assocᵉ : {o₁ o₂ o₃ o₄ : Obj C} (f : ΣS o₁ o₂) (g : ΣS o₂ o₃) (h : ΣS o₃ o₄) ->
        ((f Σ⋆ g) Σ⋆ h) == (f Σ⋆ (g Σ⋆ h))
      Σ⋆-assocᵉ f g h =
        ΣS-path (cong fst (⇒⋆ >=> cong (_Σ'⋆ (⇒ h)) ⇒⋆) >=>
                 ⋆-assoc >=>
                 cong fst (sym (cong ((⇒ f) Σ'⋆_) ⇒⋆) >=> sym ⇒⋆))

      isSet-ΣS : {o₁ o₂ : Obj C} -> isSet (ΣS o₁ o₂)
      isSet-ΣS = ≃-isSet (equiv⁻¹ (SC.eq _ _)) (isSetΣ isSet-Mor (\_ -> isProp->isSet Sub.isProp-S))


  CategoryStr-ΣSub : CategoryStr ΣS
  CategoryStr-ΣSub = record
    { id = Σid
    ; _⋆_ = _Σ⋆_
    ; ⋆-left-idᵉ = Σ⋆-left-idᵉ
    ; ⋆-right-idᵉ = Σ⋆-right-idᵉ
    ; ⋆-assocᵉ = Σ⋆-assocᵉ
    ; isSet-Mor = isSet-ΣS
    }
