{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import equality-path
open import category.base
open import hlevel.base
open import hlevel.sigma

module category.displayed where

record PreCategoryᴰ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (ℓOᴰ ℓMᴰ : Level) :
  Type (ℓ-max* 3 ℓO ℓM (ℓ-suc (ℓ-max ℓOᴰ ℓMᴰ))) where
  private
    module C = PreCategory C

  -- Sorts
  field
    Objᴰ : (c : Obj C) -> Type ℓOᴰ
    Morᴰ : {a b : Obj C} (f : C [ a , b ]) (c : Objᴰ a) (d : Objᴰ b) -> Type ℓMᴰ

  -- Operations
  field
    idᴰ : {c : Obj C} {d : Objᴰ c} -> Morᴰ (id C) d d
    _⋆ᴰ_ : {a b c : Obj C} {f : C [ a , b ]} {g : C [ b , c ]}
           {aᴰ : Objᴰ a} {bᴰ : Objᴰ b} {cᴰ : Objᴰ c}
           (fᴰ : Morᴰ f aᴰ bᴰ) (gᴰ : Morᴰ g bᴰ cᴰ) ->
           Morᴰ (f ⋆⟨ C ⟩ g) aᴰ cᴰ

  -- Laws
  field
    ⋆ᴰ-left-id :
      {s t : Obj C} {f : C [ s , t ]} {sᴰ : Objᴰ s} {tᴰ : Objᴰ t}
      (fᴰ : Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> Morᴰ (C.⋆-left-id f i) sᴰ tᴰ) (idᴰ ⋆ᴰ fᴰ) fᴰ
    ⋆ᴰ-right-id :
      {s t : Obj C} {f : C [ s , t ]} {sᴰ : Objᴰ s} {tᴰ : Objᴰ t}
      (fᴰ : Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> Morᴰ (C.⋆-right-id f i) sᴰ tᴰ) (fᴰ ⋆ᴰ idᴰ) fᴰ
    ⋆ᴰ-assoc :
      {a b c d : Obj C} {f : C [ a , b ]} {g : C [ b , c ]} {h : C [ c , d ]}
      {aᴰ : Objᴰ a} {bᴰ : Objᴰ b} {cᴰ : Objᴰ c} {dᴰ : Objᴰ d}
      (fᴰ : Morᴰ f aᴰ bᴰ) (gᴰ : Morᴰ g bᴰ cᴰ) (hᴰ : Morᴰ h cᴰ dᴰ) ->
      PathP (\i -> Morᴰ (C.⋆-assoc f g h i) aᴰ dᴰ)
            ((fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ) (fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ))
    isSet-Morᴰ :
      {a b : Obj C} {f : C [ a , b ]} {aᴰ : Objᴰ a} {bᴰ : Objᴰ b} ->
      isSet (Morᴰ f aᴰ bᴰ)


module _ {ℓO ℓM ℓOᴰ ℓMᴰ : Level} {C : PreCategory ℓO ℓM} (D : PreCategoryᴰ C ℓOᴰ ℓMᴰ) where
  private
    module D = PreCategoryᴰ D
    module C = PreCategory C

  TotalC : PreCategory (ℓ-max ℓO ℓOᴰ) (ℓ-max ℓM ℓMᴰ)
  TotalC = Laws->Category laws
    where
    sorts : CategorySorts (ℓ-max ℓO ℓOᴰ) (ℓ-max ℓM ℓMᴰ)
    sorts .CategorySorts.Obj = Σ (Obj C) D.Objᴰ
    sorts .CategorySorts.Mor (c1 , d1) (c2 , d2) =
      Σ[ f ∈ C [ c1 , c2 ] ] D.Morᴰ f d1 d2

    ops : CategoryOps sorts
    ops .CategoryOps.id = (id C , D.idᴰ)
    ops .CategoryOps._⋆_ (f , f') (g , g') = (f ⋆⟨ C ⟩ g) , (f' D.⋆ᴰ g')

    laws : CategoryLaws ops
    laws .CategoryLaws.⋆-left-id (f , f') =
      (\i -> C.⋆-left-id f i , D.⋆ᴰ-left-id f' i)
    laws .CategoryLaws.⋆-right-id (f , f') =
      (\i -> C.⋆-right-id f i , D.⋆ᴰ-right-id f' i)
    laws .CategoryLaws.⋆-assoc (f , f') (g , g') (h , h') =
      (\i -> C.⋆-assoc f g h i , D.⋆ᴰ-assoc f' g' h' i)
    laws .CategoryLaws.isSet-Mor =
      isSetΣ (isSet-Mor C) (\_ -> D.isSet-Morᴰ)


module _ {ℓO ℓM ℓOᴰ₁ ℓMᴰ₁ ℓOᴰ₂ ℓMᴰ₂ : Level} {C : PreCategory ℓO ℓM}
         (D₁ : PreCategoryᴰ C ℓOᴰ₁ ℓMᴰ₁)
         (D₂ : PreCategoryᴰ (TotalC D₁) ℓOᴰ₂ ℓOᴰ₂) where
  private
    module D₁ = PreCategoryᴰ D₁
    module D₂ = PreCategoryᴰ D₂

  TotalCᴰ : PreCategoryᴰ C (ℓ-max ℓOᴰ₁ ℓOᴰ₂) (ℓ-max* 2 ℓOᴰ₂ ℓMᴰ₁)
  TotalCᴰ .PreCategoryᴰ.Objᴰ c = Σ[ d ∈ (D₁.Objᴰ c) ] (D₂.Objᴰ (c , d))
  TotalCᴰ .PreCategoryᴰ.Morᴰ f (d₁ , d₂) (e₁ , e₂) =
    Σ[ f' ∈ D₁.Morᴰ f d₁ e₁ ] (D₂.Morᴰ (f , f') d₂ e₂)
  TotalCᴰ .PreCategoryᴰ.idᴰ = D₁.idᴰ , D₂.idᴰ
  TotalCᴰ .PreCategoryᴰ._⋆ᴰ_ (f₁ , f₂) (g₁ , g₂) = (f₁ D₁.⋆ᴰ g₁) , (f₂ D₂.⋆ᴰ g₂)
  TotalCᴰ .PreCategoryᴰ.⋆ᴰ-left-id (f₁ , f₂) =
    (\i -> D₁.⋆ᴰ-left-id f₁ i , D₂.⋆ᴰ-left-id f₂ i)
  TotalCᴰ .PreCategoryᴰ.⋆ᴰ-right-id (f₁ , f₂) =
    (\i -> D₁.⋆ᴰ-right-id f₁ i , D₂.⋆ᴰ-right-id f₂ i)
  TotalCᴰ .PreCategoryᴰ.⋆ᴰ-assoc (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) =
    (\i -> D₁.⋆ᴰ-assoc f₁ g₁ h₁ i , D₂.⋆ᴰ-assoc f₂ g₂ h₂ i)
  TotalCᴰ .PreCategoryᴰ.isSet-Morᴰ =
    isSetΣ D₁.isSet-Morᴰ (\_ -> D₂.isSet-Morᴰ)
