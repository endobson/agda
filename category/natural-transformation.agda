{-# OPTIONS --cubical --safe --exact-split #-}

module category.natural-transformation where

open import base
open import category.base
open import category.functor
open import cubical
open import equality-path
open import hlevel

-- Natural Transformations

private
  module _
    {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
    {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
    (F G : Functor C D) where

    NT-obj-Type : Type (ℓ-max* 2 ℓObjC ℓMorD)
    NT-obj-Type = (c : Obj C) -> D [ F-obj F c , F-obj G c ]
    NT-mor-Type : NT-obj-Type -> Type (ℓ-max* 3 ℓObjC ℓMorC ℓMorD)
    NT-mor-Type obj = {x y : Obj C} -> (f : C [ x , y ]) ->
                      obj x ⋆⟨ D ⟩ F-mor G f == F-mor F f ⋆⟨ D ⟩ obj y

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  (F G : Functor C D) where

  record NaturalTransformation : Type (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD) where
    field
      obj : NT-obj-Type F G
      mor : NT-mor-Type F G obj

open NaturalTransformation public renaming
  ( obj to NT-obj
  ; mor to NT-mor
  )

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  {F G : Functor C D} where

  natural-transformation-path :
    {nt1 nt2 : NaturalTransformation F G} ->
    NaturalTransformation.obj nt1 == NaturalTransformation.obj nt2 ->
    nt1 == nt2
  natural-transformation-path {nt1} {nt2} op i = record
    { obj = op i
    ; mor = sq i
    }
    where
    sq : PathP (\i -> NT-mor-Type F G (op i))
               (NaturalTransformation.mor nt1)
               (NaturalTransformation.mor nt2)
    sq = isProp->PathP (\i -> isPropΠⁱ2 (\x y -> isPropΠ (\f -> isSet-Mor D _ _)))


  isSet-NaturalTransformation : isSet (NaturalTransformation F G)
  isSet-NaturalTransformation nt1 nt2 p1 p2 = p1=p2
    where
    o1 = NT-obj nt1
    o2 = NT-obj nt2
    m1 = NT-mor nt1
    m2 = NT-mor nt2

    op1 : o1 == o2
    op1 i = NT-obj (p1 i)

    mp1 : PathP (\i -> NT-mor-Type F G (op1 i)) m1 m2
    mp1 i = NT-mor (p1 i)

    op2 : o1 == o2
    op2 i = NT-obj (p2 i)

    mp2 : PathP (\i -> NT-mor-Type F G (op2 i)) m1 m2
    mp2 i = NT-mor (p2 i)

    op1=op2 : op1 == op2
    op1=op2 = isSetΠ (\_ -> isSet-Mor D) o1 o2 op1 op2

    isSet-NT-mor : (o : NT-obj-Type F G) -> isSet (NT-mor-Type F G o)
    isSet-NT-mor o = isSetΠⁱ (\_ -> isSetΠⁱ (\_ -> isSetΠ (\_ -> isProp->isSet (isSet-Mor D _ _))))

    mp1=mp2 : PathP (\i -> PathP (\j -> NT-mor-Type F G (op1=op2 i j)) m1 m2) mp1 mp2
    mp1=mp2 = isOfHLevel->isOfHLevelDep 2 isSet-NT-mor m1 m2 mp1 mp2 op1=op2

    op1=op2' : (i : I) -> (op1 i) == (op2 i)
    op1=op2' i j = op1=op2 j i

    p1=p2' : (i : I) -> (p1 i) == (p2 i)
    p1=p2' i = natural-transformation-path (op1=op2' i)

    p1=p2 : p1 == p2
    p1=p2 i j .NaturalTransformation.obj = op1=op2 i j
    p1=p2 i j .NaturalTransformation.mor = mp1=mp2 i j
