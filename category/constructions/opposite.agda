{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.functor
open import category.natural-transformation
open import category.univalent
open import equality-path
open import equality.identity-system

module category.constructions.opposite where

module _ {ℓo ℓm : Level} (C : PreCategory ℓo ℓm) where
  private
    module C = PreCategory C

  OpCat : PreCategory ℓo ℓm
  OpCat = record
    { Obj = C.Obj
    ; Mor = OpMor
    ; id = C.id
    ; _⋆_ = \ f g -> g ⋆⟨ C ⟩ f
    ; ⋆-left-id = \f -> C.⋆-right-id f
    ; ⋆-right-id = \f -> C.⋆-left-id f
    ; ⋆-assoc = \ f g h -> sym (C.⋆-assoc h g f)
    ; isSet-Mor = C.isSet-Mor
    }
    where
    OpMor : (s t : C.Obj) -> Type ℓm
    OpMor s t = C [ t , s ]

module _ {ℓCo ℓCm ℓDo ℓDm : Level} {C : PreCategory ℓCo ℓCm} {D : PreCategory ℓDo ℓDm}
         (F : Functor C D) where
  private
    module F = Functor F

  opF : Functor (OpCat C) (OpCat D)
  opF .F-obj o = F.obj o
  opF .F-mor f = F.mor f
  opF .F-id o = F.id o
  opF .F-⋆ f g = F.⋆ g f

module _ {ℓCo ℓCm ℓDo ℓDm : Level} {C : PreCategory ℓCo ℓCm} {D : PreCategory ℓDo ℓDm}
         {F : Functor C D} {G : Functor C D} where

  opNT : NaturalTransformation F G -> NaturalTransformation (opF G) (opF F)
  opNT nt = record
    { obj = NT-obj nt
    ; mor = \m -> sym (NT-mor nt m)
    }

private
  OpCat-twice : {ℓo ℓm : Level} {C : PreCategory ℓo ℓm} -> OpCat (OpCat C) == C
  OpCat-twice = refl

  opF-twice : {ℓCo ℓCm ℓDo ℓDm : Level}
              {C : PreCategory ℓCo ℓCm} {D : PreCategory ℓDo ℓDm}
              {F : Functor C D}
              -> opF (opF F) == F
  opF-twice = refl

  opNT-twice : {ℓCo ℓCm ℓDo ℓDm : Level}
               {C : PreCategory ℓCo ℓCm} {D : PreCategory ℓDo ℓDm}
               {F : Functor C D} {G : Functor C D}
               {nt : NaturalTransformation F G}
               -> opNT (opNT nt) == nt
  opNT-twice = refl

private
  module _ {ℓo ℓm : Level} {C : PreCategory ℓo ℓm} where
    swap-CatIso : {c1 c2 : Obj C} -> (CatIso C c1 c2) -> (CatIso (OpCat C) c1 c2)
    swap-CatIso ci .CatIso.mor = CatIso.inv ci
    swap-CatIso ci .CatIso.inv = CatIso.mor ci
    swap-CatIso ci .CatIso.sec = CatIso.sec ci
    swap-CatIso ci .CatIso.ret = CatIso.ret ci

module _ {ℓo ℓm : Level} {C : PreCategory ℓo ℓm} where
  open isIdentitySystem

  isUnivalent-OpCat : isUnivalent' C -> isUnivalent' (OpCat C)
  isUnivalent-OpCat univ = record { to-path = base-path ; to-path-over = over-path }
    where
    C' = OpCat C
    module _ {c1 c2 : Obj C} (ci' : CatIso C' c1 c2) where

      ci : CatIso C c1 c2
      ci = swap-CatIso ci'

      base-path : c1 == c2
      base-path = univ .to-path ci

      -- TODO make id² primitive
      over-path : PathP (\i -> CatIso C' c1 (base-path i)) (idCatIso C' c1) ci'
      over-path =
        transP-mid
          (cat-iso-path refl)
          (\i -> swap-CatIso (univ .to-path-over ci i))
          (cat-iso-path refl)
