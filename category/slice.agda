{-# OPTIONS --cubical --safe --exact-split #-}

module category.slice where

open import base
open import category.base
open import equality-path
open import sigma.base
open import hlevel
open import hlevel.sigma

private
  variable
    ℓObj ℓMor : Level

module _ (C : PreCategory ℓObj ℓMor) {{isCat : isCategory C}} (c : C .Obj) where
  private
    module C = PreCategory C

  record SliceObj : Type (ℓ-max ℓObj ℓMor) where
    constructor slice-obj
    field
      {obj} : C.Obj
      mor : C [ obj , c ]

  SliceC : PreCategory (ℓ-max ℓObj ℓMor) ℓMor
  SliceC .PreCategory.Obj = SliceObj
  SliceC .PreCategory.Mor (slice-obj {x} f) (slice-obj {y} g) =
    Σ[ h ∈ C [ x , y ] ] (h ⋆⟨ C ⟩ g == f)
  SliceC .PreCategory.id = C .id , C.⋆-left-id _
  SliceC .PreCategory._⋆_ (f , p) (g , q) =
    (f ⋆⟨ C ⟩ g , C.⋆-assoc _ _ _ >=> cong (f C.⋆_) q >=> p)
  SliceC .PreCategory.⋆-left-id (f , _) =
    ΣProp-path (isSet-Mor _ _) (C.⋆-left-id f)
  SliceC .PreCategory.⋆-right-id (f , _) =
    ΣProp-path (isSet-Mor _ _) (C.⋆-right-id f)
  SliceC .PreCategory.⋆-assoc (f , _) (g , _) (h , _) =
    ΣProp-path (isSet-Mor _ _) (C.⋆-assoc f g h)

  abstract
    isCategory-SliceC : isCategory SliceC
    isCategory-SliceC .isCategory.isSet-Mor = isSetΣ isSet-Mor (\h -> isProp->isSet (isSet-Mor _ _))
