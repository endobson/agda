{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import equality-path
open import category.base
open import category.instances.product
open import category.instances.opposite
open import category.instances.small
open import category.set
open import hlevel
open import funext

import functions

module category.hom-functor where


module _ {ℓ : Level} (C : PreCategory ℓ ℓ) {{isCat-C : isCategory C}} where
  private
    C2 : PreCategory ℓ ℓ
    C2 = (ProductCat (OpCat C) C)
    module C = PreCategory C

  hom-functor : Functor C2 (SetC ℓ)
  hom-functor = record
    { F-obj = homObj
    ; F-mor = homMor
    ; F-id = homId
    ; F-⋆ = hom⋆
    }
    where
    homObj : Obj C2 -> Obj (SetC ℓ)
    homObj (a , b) = C [ a , b ] , isSet-Mor

    homMor : {a b : Obj C2} -> C2 [ a , b ] -> (SetC ℓ) [ homObj a , homObj b ]
    homMor (f , g) = set-function (\h -> (f ⋆⟨ C ⟩ h ⋆⟨ C ⟩ g))

    homId : (a : Obj C2) -> homMor (idᵉ C2 a) == id (SetC ℓ)
    homId a = cong set-function (funExt (\f -> C.⋆-right-id _ >=> C.⋆-left-id _))

    hom⋆ : {x y z : Obj C2} -> (f : C2 [ x , y ]) -> (g : C2 [ y , z ]) ->
           homMor (f ⋆⟨ C2 ⟩ g) == (homMor f ⋆⟨ SetC ℓ ⟩ homMor g)
    hom⋆ (f1 , f2) (g1 , g2) = cong set-function (funExt ans)
      where
      ans : ∀ h -> ((g1 ⋆⟨ C ⟩ f1) ⋆⟨ C ⟩ h ⋆⟨ C ⟩ (f2 ⋆⟨ C ⟩ g2)) == 
                   (g1 ⋆⟨ C ⟩ (f1 ⋆⟨ C ⟩ h ⋆⟨ C ⟩ f2) ⋆⟨ C ⟩ g2)
      ans h = sym (C.⋆-assoc _ _ _) >=> 
              cong (\f -> f ⋆⟨ C ⟩ g2) 
                   (C.⋆-assoc _ _ _ >=> 
                    C.⋆-assoc _ _ _ >=> 
                    cong (\f -> g1 ⋆⟨ C ⟩ f) 
                         (sym (C.⋆-assoc _ _ _)))

  hom-functor-source : Obj C -> Functor C (SetC ℓ)
  hom-functor-source o = functor-compose raise hom-functor
    where
    raise : Functor C C2
    raise = record 
      { F-obj = \x -> o , x
      ; F-mor = \m -> id C , m
      ; F-id = \x -> refl
      ; F-⋆ = \f g -> cong2 _,_ (sym (C.⋆-left-id _)) refl
      }


  hom-functor-target : Obj C -> Functor (OpCat C) (SetC ℓ)
  hom-functor-target o = functor-compose raise hom-functor
    where
    raise : Functor (OpCat C) C2
    raise = record 
      { F-obj = \x -> x , o
      ; F-mor = \m -> m , id C
      ; F-id = \x -> refl
      ; F-⋆ = \f g -> cong2 _,_ refl (sym (C.⋆-left-id _))
      }


