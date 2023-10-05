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
  {F1 F2 G1 G2 : Functor C D}
  {pF : F1 == F2} {pG : G1 == G2} where

  natural-transformation-pathp :
    {nt1 : NaturalTransformation F1 G1} ->
    {nt2 : NaturalTransformation F2 G2} ->
    ((c : Obj C) ->
      PathP (\i -> D [ F-obj (pF i) c , F-obj (pG i) c ])
        (NaturalTransformation.obj nt1 c) (NaturalTransformation.obj nt2 c)) ->
    PathP (\i -> NaturalTransformation (pF i) (pG i)) nt1 nt2
  natural-transformation-pathp {nt1} {nt2} op i = record
    { obj = \c -> op c i
    ; mor = sq i
    }
    where
    sq : PathP (\i -> NT-mor-Type (pF i) (pG i) (\c -> op c i))
               (NaturalTransformation.mor nt1)
               (NaturalTransformation.mor nt2)
    sq = isProp->PathP (\i -> isPropΠⁱ2 (\x y -> isPropΠ (\f -> isSet-Mor D _ _)))

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  {F G : Functor C D} where

  natural-transformation-path :
    {nt1 nt2 : NaturalTransformation F G} ->
    ((c : Obj C) -> NaturalTransformation.obj nt1 c == NaturalTransformation.obj nt2 c) ->
    nt1 == nt2
  natural-transformation-path = natural-transformation-pathp

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

    p1=p2' : (i : I) -> (p1 i) == (p2 i)
    p1=p2' i = natural-transformation-path (\c j -> op1=op2 j i c)

    p1=p2 : p1 == p2
    p1=p2 i j .NaturalTransformation.obj = op1=op2 i j
    p1=p2 i j .NaturalTransformation.mor = mp1=mp2 i j


module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
         {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD} where
  private
    module D = PreCategory D

  id-NT : (F : Functor C D) -> NaturalTransformation F F
  id-NT F .NaturalTransformation.obj x = id D
  id-NT F .NaturalTransformation.mor f =
    D.⋆-left-id _ >=> sym (D.⋆-right-id _)

  -- Vertical composition
  _⋆NT_ : {F G H : Functor C D} -> NaturalTransformation F G ->
          NaturalTransformation G H -> NaturalTransformation F H
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

  ⋆NT-left-id : {F G : Functor C D} -> (nt : NaturalTransformation F G) ->
                (id-NT F) ⋆NT nt == nt
  ⋆NT-left-id nt = natural-transformation-path (\x -> (D.⋆-left-id (NT-obj nt x)))

  ⋆NT-right-id : {F G : Functor C D} -> (nt : NaturalTransformation F G) ->
                 nt ⋆NT (id-NT G) == nt
  ⋆NT-right-id nt = natural-transformation-path (\x -> (D.⋆-right-id (NT-obj nt x)))

  ⋆NT-assoc :
    {F G H I : Functor C D} ->
    (nt1 : NaturalTransformation F G) ->
    (nt2 : NaturalTransformation G H) ->
    (nt3 : NaturalTransformation H I) ->
    (nt1 ⋆NT nt2) ⋆NT nt3 == nt1 ⋆NT (nt2 ⋆NT nt3)
  ⋆NT-assoc nt1 nt2 nt3 = natural-transformation-path (\x -> (D.⋆-assoc _ _ _))

module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME}
         {f1 : Functor C D}
         {f2 : Functor C D}
         {f3 : Functor D E}
         {f4 : Functor D E} where
  _⋆NTʰ_ : NaturalTransformation f1 f2 ->
           NaturalTransformation f3 f4 ->
           NaturalTransformation (f1 ⋆F f3) (f2 ⋆F f4)
  _⋆NTʰ_ nt12 nt34 = record
    { obj = \ c -> nt34.obj (F-obj f1 c) ⋆⟨ E ⟩ F-mor f4 (nt12.obj c)
    ; mor = mor
    }
    where
    module f3 = Functor f3
    module E = CategoryHelpers E
    module nt12 = NaturalTransformation nt12
    module nt34 = NaturalTransformation nt34
    opaque
      mor : {x y : Obj C} (m : C [ x , y ]) -> _
      mor m =
        E.⋆-left (nt34.mor (nt12.obj _)) >=>
        E.⋆-assoc >=>
        E.⋆-right (nt34.mor _) >=>
        sym E.⋆-assoc >=>
        E.⋆-left (sym (f3.⋆ _ _) >=> cong f3.mor (nt12.mor _) >=>
                   f3.⋆ _ _) >=>
        E.⋆-assoc >=>
        E.⋆-right (sym (nt34.mor _))

module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME}
         {f1 : Functor C D}
         {f2 : Functor C D}
         {f3 : Functor C D}
         {f4 : Functor D E}
         {f5 : Functor D E}
         {f6 : Functor D E}
         where
  ⋆NTʰ-⋆NT : (nt12 : NaturalTransformation f1 f2)
             (nt45 : NaturalTransformation f4 f5)
             (nt23 : NaturalTransformation f2 f3)
             (nt56 : NaturalTransformation f5 f6) ->
             (nt12 ⋆NT nt23) ⋆NTʰ (nt45 ⋆NT nt56) ==
             (nt12 ⋆NTʰ nt45) ⋆NT (nt23 ⋆NTʰ nt56)
  ⋆NTʰ-⋆NT nt12 nt45 nt23 nt56 = natural-transformation-path ans
    where
    opaque
      ans : ∀ c ->
        (NT-obj nt45 (F-obj f1 c) ⋆⟨ E ⟩ NT-obj nt56 (F-obj f1 c)) ⋆⟨ E ⟩
        (F-mor f6 ((NT-obj nt12 c) ⋆⟨ D ⟩ (NT-obj nt23 c))) ==
        (NT-obj nt45 (F-obj f1 c) ⋆⟨ E ⟩ F-mor f5 (NT-obj nt12 c)) ⋆⟨ E ⟩
        (NT-obj nt56 (F-obj f2 c) ⋆⟨ E ⟩ F-mor f6 (NT-obj nt23 c))
      ans c =
        ⋆-right (F-⋆ f6 _ _) >=>
        sym ⋆-assoc >=>
        ⋆-left (⋆-assoc >=> ⋆-right (NT-mor nt56 _) >=> sym ⋆-assoc) >=>
        ⋆-assoc
        where
        open CategoryHelpers E

module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME} where
  open CategoryHelpers E

  _NT▶_ : {f1 f2 : Functor C D} -> NaturalTransformation f1 f2 -> (f3 : Functor D E) ->
          NaturalTransformation (f1 ⋆F f3) (f2 ⋆F f3)
  _NT▶_ nt f3 = record
    { obj = \c -> F-mor f3 (NT-obj nt c)
    ; mor = \m -> sym (F-⋆ f3 _ _) >=> cong (F-mor f3) (NT-mor nt _) >=> (F-⋆ f3 _ _)
    }

  _NT◀_ : (f1 : Functor C D) -> {f2 f3 : Functor D E} -> NaturalTransformation f2 f3 ->
          NaturalTransformation (f1 ⋆F f2) (f1 ⋆F f3)
  _NT◀_ f1 nt = record
    { obj = \c -> (NT-obj nt (F-obj f1 c))
    ; mor = \m -> (NT-mor nt _)
    }

  -- Version of NT▶ and NT◀ that match up with ⋆NTʰ.
  _NT▶'_ : {f1 f2 : Functor C D} -> NaturalTransformation f1 f2 -> (f3 : Functor D E) ->
           NaturalTransformation (f1 ⋆F f3) (f2 ⋆F f3)
  _NT▶'_ nt f3 = nt ⋆NTʰ (id-NT f3)

  _NT◀'_ : (f1 : Functor C D) -> {f2 f3 : Functor D E} -> NaturalTransformation f2 f3 ->
           NaturalTransformation (f1 ⋆F f2) (f1 ⋆F f3)
  _NT◀'_ f1 nt = (id-NT f1) ⋆NTʰ nt

  NT▶'-path : {f1 f2 : Functor C D} (nt : NaturalTransformation f1 f2) (f3 : Functor D E) ->
              (nt NT▶' f3) == (nt NT▶ f3)
  NT▶'-path nt f3 = natural-transformation-path (\c -> ⋆-left-id)

  NT◀'-path : (f1 : Functor C D) {f2 f3 : Functor D E} (nt : NaturalTransformation f2 f3)  ->
              (f1 NT◀' nt) == (f1 NT◀ nt)
  NT◀'-path f1 {f2} {f3} nt =
    natural-transformation-path (\c -> ⋆-right (F-id f3 _) >=> ⋆-right-id)

module _ {ℓOC ℓMC ℓOD ℓMD : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD} where
  NT▶-id : {f1 f2 : Functor C D} -> (nt : NaturalTransformation f1 f2) ->
           PathP (\ i -> NaturalTransformation (⋆F-right-id f1 i) (⋆F-right-id f2 i))
             (nt NT▶ idF D) nt
  NT▶-id nt = (natural-transformation-pathp (\c -> refl))

  NT◀-id : {f1 f2 : Functor C D} -> (nt : NaturalTransformation f1 f2) ->
           PathP (\ i -> NaturalTransformation (⋆F-left-id f1 i) (⋆F-left-id f2 i))
             (idF C NT◀ nt) nt
  NT◀-id nt = (natural-transformation-pathp (\c -> refl))
