{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.functor
open import equality-path

module category.instances.small where


module _ {ℓAo ℓAm ℓBo ℓBm ℓCo ℓCm : Level}
         {A : PreCategory ℓAo ℓAm}
         {B : PreCategory ℓBo ℓBm}
         {C : PreCategory ℓCo ℓCm}
         (F : Functor A B) (G : Functor B C) where
  functor-compose : Functor A C
  functor-compose = record
    { obj = \o -> G.obj (F.obj o)
    ; mor = \m -> G.mor (F.mor m)
    ; id = \m -> cong G.mor (F.id m) >=> G.id _
    ; ⋆ = \f g -> cong G.mor (F.⋆ f g) >=> G.⋆ _ _
    }
    where
    module F = Functor F
    module G = Functor G

module _ {ℓo ℓm : Level} (C : PreCategory ℓo ℓm) where
  id-functor : Functor C C
  id-functor = record
    { obj = \o -> o
    ; mor = \m -> m
    ; id = \_ -> refl
    ; ⋆ = \_ _ -> refl
    }


module _ (ℓo ℓm : Level) where
  private
    ℓ : Level
    ℓ = (ℓ-max ℓo ℓm)
    CatObj : Type (ℓ-suc ℓ)
    CatObj = (PreCategory ℓo ℓm)
    CatMor : (s t : CatObj) -> Type ℓ
    CatMor s t = Functor s t

    Cat-id : (s : CatObj) -> CatMor s s
    Cat-id = id-functor

    Cat-⋆ : {s t u : CatObj} -> CatMor s t -> CatMor t u -> CatMor s u
    Cat-⋆ = functor-compose

    Cat-⋆-left-id : {s t : CatObj} -> (m : CatMor s t) -> Cat-⋆ (Cat-id s) m == m
    Cat-⋆-left-id F i .F-obj = F-obj F
    Cat-⋆-left-id F i .F-mor = F-mor F
    Cat-⋆-left-id F i .F-id m = compPath-refl-left (F-id F m) i
    Cat-⋆-left-id F i .F-⋆ f g = compPath-refl-left (F-⋆ F f g) i

    Cat-⋆-right-id : {s t : CatObj} -> (m : CatMor s t) -> Cat-⋆ m (Cat-id t) == m
    Cat-⋆-right-id F i .F-obj = F-obj F
    Cat-⋆-right-id F i .F-mor = F-mor F
    Cat-⋆-right-id F i .F-id m = compPath-refl-right (F-id F m) i
    Cat-⋆-right-id F i .F-⋆ f g = compPath-refl-right (F-⋆ F f g) i

    module _ {s t u v : CatObj} (F : CatMor s t) (G : CatMor t u) (H : CatMor u v) where
      private
        module F = Functor F
        module G = Functor G
        module H = Functor H

      Cat-⋆-assoc : (Cat-⋆ (Cat-⋆ F G) H) == (Cat-⋆ F (Cat-⋆ G H))
      Cat-⋆-assoc i .F-obj = \o -> H.obj (G.obj (F.obj o))
      Cat-⋆-assoc i .F-mor = \m -> H.mor (G.mor (F.mor m))
      Cat-⋆-assoc i .F-id x = ans i
        where
        ans : (cong H.mor (cong G.mor (F.id _) >=> G.id _) >=> H.id _) ==
              (cong (\m -> H.mor (G.mor m)) (F.id _) >=> (cong H.mor (G.id _) >=> H.id _))
        ans = (cong (_>=> H.id _) (sym (cong-trans H.mor _ _))) >=>
              (compPath-assoc _ _ _)

      Cat-⋆-assoc i .F-⋆ f g = ans i
        where
        ans : (cong H.mor (cong G.mor (F.⋆ _ _) >=> G.⋆ _ _) >=> H.⋆ _ _) ==
              (cong (\m -> H.mor (G.mor m)) (F.⋆ _ _) >=> (cong H.mor (G.⋆ _ _) >=> H.⋆ _ _))
        ans = (cong (_>=> H.⋆ _ _) (sym (cong-trans H.mor _ _))) >=>
              (compPath-assoc _ _ _)

  -- CatC : PreCategory (ℓ-suc ℓ) ℓ
  -- CatC = record
  --   { Obj = CatObj
  --   ; Mor = CatMor
  --   ; id = Cat-id _
  --   ; _⋆_ = Cat-⋆
  --   ; ⋆-left-id = Cat-⋆-left-id
  --   ; ⋆-right-id = Cat-⋆-right-id
  --   ; ⋆-assoc = Cat-⋆-assoc
  --   ; isSet-Mor = isSet-Functor
  --   }
