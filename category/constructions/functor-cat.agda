{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.functor-cat where

open import base
open import category.base
open import category.functor
open import category.natural-transformation
open import cubical
open import equality-path
open import funext
open import hlevel

module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
         {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD} where
  private
    module D = PreCategory D

  id-NT : (F : Functor C D) -> NaturalTransformation F F
  id-NT F .NaturalTransformation.obj x = id D
  id-NT F .NaturalTransformation.mor f =
    D.⋆-left-id _ >=> sym (D.⋆-right-id _)

  -- Vertical composition
  _⋆NT_ : {F G H : Functor C D} ->
          NaturalTransformation F G ->
          NaturalTransformation G H ->
          NaturalTransformation F H
  _⋆NT_ nt1 nt2 .NaturalTransformation.obj x =
    NT-obj nt1 x ⋆⟨ D ⟩ NT-obj nt2 x
  _⋆NT_ {F} {G} {H} nt1 nt2 .NaturalTransformation.mor {x} {y} f = ans
    where
    opaque
      ans : (NT-obj nt1 x ⋆⟨ D ⟩ NT-obj nt2 x) ⋆⟨ D ⟩ F-mor H f ==
            F-mor F f ⋆⟨ D ⟩ (NT-obj nt1 y ⋆⟨ D ⟩ NT-obj nt2 y)
      ans =
        ⋆-assoc >=>
        ⋆-cong refl (NT-mor nt2 _) >=>
        sym ⋆-assoc >=>
        ⋆-cong (NT-mor nt1 _) refl >=>
        ⋆-assoc
        where
        open CategoryHelpers D


module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
         (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) where
  private
    module C = PreCategory C
    module D = PreCategory D
    ℓF = (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD)

  private
    ⋆NT-left-id : {F G : Functor C D} -> (nt : NaturalTransformation F G) ->
                  (id-NT F) ⋆NT nt == nt
    ⋆NT-left-id nt = natural-transformation-path (funExt (\x -> (D.⋆-left-id (NT-obj nt x))))

    ⋆NT-right-id : {F G : Functor C D} -> (nt : NaturalTransformation F G) ->
                   nt ⋆NT (id-NT G) == nt
    ⋆NT-right-id nt = natural-transformation-path (funExt (\x -> (D.⋆-right-id (NT-obj nt x))))

    ⋆NT-assoc :
      {F G H I : Functor C D} ->
      (nt1 : NaturalTransformation F G) ->
      (nt2 : NaturalTransformation G H) ->
      (nt3 : NaturalTransformation H I) ->
      (nt1 ⋆NT nt2) ⋆NT nt3 == nt1 ⋆NT (nt2 ⋆NT nt3)
    ⋆NT-assoc nt1 nt2 nt3 = natural-transformation-path (funExt (\x -> (D.⋆-assoc _ _ _)))

  FunctorC : PreCategory ℓF ℓF
  FunctorC .PreCategory.Obj = Functor C D
  FunctorC .PreCategory.Mor = NaturalTransformation
  FunctorC .PreCategory.id = id-NT _
  FunctorC .PreCategory._⋆_ = _⋆NT_
  FunctorC .PreCategory.⋆-left-id = ⋆NT-left-id
  FunctorC .PreCategory.⋆-right-id = ⋆NT-right-id
  FunctorC .PreCategory.⋆-assoc = ⋆NT-assoc
  FunctorC .PreCategory.isSet-Mor = isSet-NaturalTransformation

  diagonal-functor : Functor D FunctorC
  diagonal-functor = record
    { obj = \d -> constantF C D d
    ; mor = \f -> record
      { obj = \_ -> f
      ; mor = \_ -> D.⋆-right-id _ >=> sym (D.⋆-left-id _)
      }
    ; id = \_ -> natural-transformation-path refl
    ; ⋆ = \_ _ -> natural-transformation-path refl
    }
