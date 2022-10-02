{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import equality-path

module category.instances.small where


module _ {ℓAo ℓAm ℓBo ℓBm ℓCo ℓCm : Level}
         {A : PreCategory ℓAo ℓAm}
         {B : PreCategory ℓBo ℓBm}
         {C : PreCategory ℓCo ℓCm}
         (F : Functor A B) (G : Functor B C) where
  functor-compose : Functor A C
  functor-compose = record
    { F-obj = \o -> G.F-obj (F.F-obj o)
    ; F-mor = \m -> G.F-mor (F.F-mor m)
    ; F-id = \m -> cong G.F-mor (F.F-id m) >=> G.F-id _
    ; F-⋆ = \f g -> cong G.F-mor (F.F-⋆ f g) >=> G.F-⋆ _ _
    }
    where
    module F = Functor F
    module G = Functor G

module _ {ℓo ℓm : Level} (C : PreCategory ℓo ℓm) where
  id-functor : Functor C C
  id-functor = record
    { F-obj = \o -> o
    ; F-mor = \m -> m
    ; F-id = \_ -> refl
    ; F-⋆ = \_ _ -> refl
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
      Cat-⋆-assoc i .F-obj = \o -> H.F-obj (G.F-obj (F.F-obj o))
      Cat-⋆-assoc i .F-mor = \m -> H.F-mor (G.F-mor (F.F-mor m))
      Cat-⋆-assoc i .F-id x = ans i
        where
        ans : (cong H.F-mor (cong G.F-mor (F.F-id _) >=> G.F-id _) >=> H.F-id _) ==
              (cong (\m -> H.F-mor (G.F-mor m)) (F.F-id _) >=> (cong H.F-mor (G.F-id _) >=> H.F-id _))
        ans = (cong (_>=> H.F-id _) (sym (cong-trans H.F-mor _ _))) >=> 
              (compPath-assoc _ _ _)

      Cat-⋆-assoc i .F-⋆ f g = ans i
        where
        ans : (cong H.F-mor (cong G.F-mor (F.F-⋆ _ _) >=> G.F-⋆ _ _) >=> H.F-⋆ _ _) ==
              (cong (\m -> H.F-mor (G.F-mor m)) (F.F-⋆ _ _) >=> (cong H.F-mor (G.F-⋆ _ _) >=> H.F-⋆ _ _))
        ans = (cong (_>=> H.F-⋆ _ _) (sym (cong-trans H.F-mor _ _))) >=> 
              (compPath-assoc _ _ _)

  CatC : PreCategory (ℓ-suc ℓ) ℓ
  CatC = record
    { Obj = CatObj
    ; Mor = CatMor
    ; id = Cat-id _
    ; _⋆_ = Cat-⋆
    ; ⋆-left-id = Cat-⋆-left-id
    ; ⋆-right-id = Cat-⋆-right-id
    ; ⋆-assoc = Cat-⋆-assoc
    }
