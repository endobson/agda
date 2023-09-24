{-# OPTIONS --cubical --safe --exact-split #-}

module category.natural-transformation where

open import base
open import category.base
open import category.functor
open import equality-path
open import hlevel

-- Natural Transformations

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  (F G : Functor C D) where

  NT-obj-Type : Type (ℓ-max* 2 ℓObjC ℓMorD)
  NT-obj-Type = (c : Obj C) -> D [ F-obj F c , F-obj G c ]
  NT-mor-Type : NT-obj-Type -> Type (ℓ-max* 3 ℓObjC ℓMorC ℓMorD)
  NT-mor-Type obj = {x y : Obj C} -> (f : C [ x , y ]) ->
                    obj x ⋆⟨ D ⟩ F-mor G f == F-mor F f ⋆⟨ D ⟩ obj y

  record NaturalTransformation : Type (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD) where
    field
      NT-obj : NT-obj-Type
      NT-mor : NT-mor-Type NT-obj

open NaturalTransformation public

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  {F G : Functor C D}
  {nt1 nt2 : NaturalTransformation F G} where

  natural-transformation-path :
    NaturalTransformation.NT-obj nt1 == NaturalTransformation.NT-obj nt2 ->
    nt1 == nt2
  natural-transformation-path op i = record
    { NT-obj = op i
    ; NT-mor = sq i
    }
    where
    sq : PathP (\i -> NT-mor-Type F G (op i))
               (NaturalTransformation.NT-mor nt1)
               (NaturalTransformation.NT-mor nt2)
    sq = isProp->PathP (\i -> isPropΠⁱ2 (\x y -> isPropΠ (\f -> isSet-Mor D _ _)))
