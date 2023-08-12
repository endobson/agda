{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.functor-cat where

open import base
open import category.base
open import cubical
open import equality-path
open import funext
open import hlevel

module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
         (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) where
  private
    module C = PreCategory C
    module D = PreCategory D
    ℓF = (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD)

    id-NT : (F : Functor C D) -> NaturalTransformation F F
    id-NT F .NaturalTransformation.NT-obj x = id D
    id-NT F .NaturalTransformation.NT-mor f =
      D.⋆-left-id _ >=> sym (D.⋆-right-id _)

    -- Vertical composition
    compose-NT : {F G H : Functor C D} ->
                 NaturalTransformation F G ->
                 NaturalTransformation G H ->
                 NaturalTransformation F H
    compose-NT nt1 nt2 .NaturalTransformation.NT-obj x =
      NT-obj nt1 x ⋆⟨ D ⟩ NT-obj nt2 x
    compose-NT {F} {G} {H} nt1 nt2 .NaturalTransformation.NT-mor {x} {y} f = ans
      where
      ans : (NT-obj nt1 x ⋆⟨ D ⟩ NT-obj nt2 x) ⋆⟨ D ⟩ F-mor H f ==
            F-mor F f ⋆⟨ D ⟩ (NT-obj nt1 y ⋆⟨ D ⟩ NT-obj nt2 y)
      ans =
        D.⋆-assoc _ _ _ >=>
        D.⋆-cong refl (NT-mor nt2 _) >=>
        sym (D.⋆-assoc _ _ _) >=>
        D.⋆-cong (NT-mor nt1 _) refl >=>
        D.⋆-assoc _ _ _

    extend-NT-obj-path : {F G : Functor C D} {nt1 nt2 : NaturalTransformation F G} ->
                         NT-obj nt1 == NT-obj nt2 -> nt1 == nt2
    extend-NT-obj-path op i .NaturalTransformation.NT-obj = op i
    extend-NT-obj-path {F} {G} {nt1} {nt2} op i .NaturalTransformation.NT-mor {x} {y} f = ans i
      where
      ans : PathP (\j -> op j x ⋆⟨ D ⟩ F-mor G f == F-mor F f ⋆⟨ D ⟩ op j y)
                  (NT-mor nt1 f) (NT-mor nt2 f)
      ans = isProp->PathP (\ j -> isSet-Mor D _ _)

    compose-NT-left-id : {F G : Functor C D} ->
                         (nt : NaturalTransformation F G) ->
                         compose-NT (id-NT F) nt == nt
    compose-NT-left-id nt = extend-NT-obj-path (funExt (\x -> (D.⋆-left-id (NT-obj nt x))))

    compose-NT-right-id : {F G : Functor C D} ->
                          (nt : NaturalTransformation F G) ->
                          compose-NT nt (id-NT G) == nt
    compose-NT-right-id nt = extend-NT-obj-path (funExt (\x -> (D.⋆-right-id (NT-obj nt x))))

    compose-NT-assoc :
      {F G H I : Functor C D} ->
      (nt1 : NaturalTransformation F G) ->
      (nt2 : NaturalTransformation G H) ->
      (nt3 : NaturalTransformation H I) ->
      compose-NT (compose-NT nt1 nt2) nt3 == compose-NT nt1 (compose-NT nt2 nt3)
    compose-NT-assoc nt1 nt2 nt3 = extend-NT-obj-path (funExt (\x -> (D.⋆-assoc _ _ _)))

    isSet-NaturalTransformation : {F G : Functor C D} -> isSet (NaturalTransformation F G)
    isSet-NaturalTransformation {F} {G} nt1 nt2 p1 p2 = p1=p2
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
      p1=p2' i = extend-NT-obj-path (op1=op2' i)

      p1=p2 : p1 == p2
      p1=p2 i j .NaturalTransformation.NT-obj = op1=op2 i j
      p1=p2 i j .NaturalTransformation.NT-mor = mp1=mp2 i j

  FunctorC : PreCategory ℓF ℓF
  FunctorC .PreCategory.Obj = Functor C D
  FunctorC .PreCategory.Mor = NaturalTransformation
  FunctorC .PreCategory.id = id-NT _
  FunctorC .PreCategory._⋆_ = compose-NT
  FunctorC .PreCategory.⋆-left-id = compose-NT-left-id
  FunctorC .PreCategory.⋆-right-id = compose-NT-right-id
  FunctorC .PreCategory.⋆-assoc = compose-NT-assoc
  FunctorC .PreCategory.isSet-Mor = isSet-NaturalTransformation

  constantF : (x : Obj D) -> Functor C D
  constantF x .Functor.obj = \_ -> x
  constantF x .Functor.mor = \_ -> id D
  constantF x .Functor.id  = \_ -> refl
  constantF x .Functor.⋆  = \_ _ -> sym (D.⋆-left-id _)

  diagonal-functor : Functor D FunctorC
  diagonal-functor = record
    { obj = constantF
    ; mor = \f -> record
      { NT-obj = \_ -> f
      ; NT-mor = \_ -> D.⋆-right-id _ >=> sym (D.⋆-left-id _)
      }
    ; id = \_ -> natural-transformation-path _ _ refl
    ; ⋆ = \_ _ -> natural-transformation-path _ _ refl
    }
