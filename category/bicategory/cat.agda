{-# OPTIONS --cubical --safe --exact-split #-}

module category.bicategory.cat where

open import base
open import category.base
open import category.bicategory
open import category.constructions.functor-cat
open import category.constructions.product
open import category.constructions.triple-product
open import category.functor
open import category.functor
open import category.natural-isomorphism
open import category.natural-transformation
open import equality-path
open import equivalence
open import funext


private

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

    ⋆NTʰ-⋆F : (nt12 : NaturalTransformation f1 f2)
              (nt45 : NaturalTransformation f4 f5)
              (nt23 : NaturalTransformation f2 f3)
              (nt56 : NaturalTransformation f5 f6) ->
              (nt12 ⋆NT nt23) ⋆NTʰ (nt45 ⋆NT nt56) ==
              (nt12 ⋆NTʰ nt45) ⋆NT (nt23 ⋆NTʰ nt56)
    ⋆NTʰ-⋆F nt12 nt45 nt23 nt56 = natural-transformation-path ans
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
           {E : PreCategory ℓOE ℓME}
           (f1 : Functor C D)
           (f2 : Functor D E) where
    private
      module E = CategoryHelpers E

    ⋆NTʰ-id : (id-NT f1) ⋆NTʰ (id-NT f2) == id-NT (f1 ⋆F f2)
    ⋆NTʰ-id = natural-transformation-path ans
      where
      ans : ∀ c -> id E ⋆⟨ E ⟩ (F-mor f2 (id D)) == id E
      ans c = E.⋆-left-id >=> F-id f2 (F-obj f1 c)


  module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
           {C : PreCategory ℓOC ℓMC}
           {D : PreCategory ℓOD ℓMD}
           {E : PreCategory ℓOE ℓME} where
    ⊗Cat : BiFunctor (FunctorC C D) (FunctorC D E) (FunctorC C E)
    ⊗Cat = record
      { obj = \(F , G) -> F ⋆F G
      ; mor = \(nt1 , nt2) -> nt1 ⋆NTʰ nt2
      ; id = \(F , G) -> ⋆NTʰ-id F G
      ; ⋆ = \(nt1 , nt2) (nt3 , nt4) -> ⋆NTʰ-⋆NT nt1 nt2 nt3 nt4
      }

-- TODO make this more level polymorphic
module _ {ℓO ℓM : Level}
         {A : PreCategory ℓO ℓM}
         {B : PreCategory ℓO ℓM} where
  open CategoryHelpers B

  unitorˡ-NT : NaturalTransformation (appˡ ⊗Cat (idF A)) (idF (FunctorC A B))
  unitorˡ-NT = record
    { obj = \f -> record
      { obj = \a -> id B
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
    ; mor = \{f1} {f2} m -> natural-transformation-path (\a ->
       ⋆-left-id >=>
       sym ⋆-right-id >=>
       sym (⋆-right (F-id f2 a)) >=>
       sym ⋆-right-id)
    }

  unitorˡ-isNI : isNaturalIso _ _ unitorˡ-NT
  unitorˡ-isNI f = record
    { inv = record
      { obj = \a -> id B
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
    ; sec = natural-transformation-path (\a -> ⋆-left-id)
    ; ret = natural-transformation-path (\a -> ⋆-left-id)
    }

  unitorʳ-NT : NaturalTransformation (appʳ ⊗Cat (idF B)) (idF (FunctorC A B))
  unitorʳ-NT = record
    { obj = \f -> record
      { obj = \a -> id B
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
    ; mor = \f -> natural-transformation-path (\m -> sym ⋆-right-id)
    }

  unitorʳ-isNI : isNaturalIso _ _ unitorʳ-NT
  unitorʳ-isNI f = record
    { inv = record
      { obj = \a -> id B
      ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
      }
    ; sec = natural-transformation-path (\_ -> ⋆-right-id)
    ; ret = natural-transformation-path (\_ -> ⋆-right-id)
    }

module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME ℓOF ℓMF : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME}
         {F : PreCategory ℓOF ℓMF}
         where
  open CategoryHelpers F

  ⋆F-assoc-NT : (f1 : Functor C D) (f2 : Functor D E) (f3 : Functor E F) ->
                NaturalTransformation ((f1 ⋆F f2) ⋆F f3) (f1 ⋆F (f2 ⋆F f3))
  ⋆F-assoc-NT f1 f2 f3 = record
    { obj = \a -> id F
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }

  ⋆F-assoc-NT' : (f1 : Functor C D) (f2 : Functor D E) (f3 : Functor E F) ->
                 NaturalTransformation (f1 ⋆F (f2 ⋆F f3)) ((f1 ⋆F f2) ⋆F f3)
  ⋆F-assoc-NT' f1 f2 f3 = record
    { obj = \a -> id F
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }

  ⋆F-assoc-NI : (f1 : Functor C D) (f2 : Functor D E) (f3 : Functor E F) ->
                NaturalIsomorphism ((f1 ⋆F f2) ⋆F f3) (f1 ⋆F (f2 ⋆F f3))
  ⋆F-assoc-NI f1 f2 f3 =
    ⋆F-assoc-NT f1 f2 f3 , eqFun (isNaturalIso'≃isNaturalIso _ _) inner
    where
    inner : isNaturalIso' _ _ (⋆F-assoc-NT f1 f2 f3)
    inner = record
      { inv = ⋆F-assoc-NT' f1 f2 f3
      ; sec = natural-transformation-path (\_ -> ⋆-id²)
      ; ret = natural-transformation-path (\_ -> ⋆-id²)
      }

private
  module _ {ℓO ℓM : Level}
           {A : PreCategory ℓO ℓM}
           {B : PreCategory ℓO ℓM}
           {C : PreCategory ℓO ℓM}
           {D : PreCategory ℓO ℓM}
           where
    open CategoryHelpers D

    private
     lF = LeftBiasedDoubleApplicationFunctor
            (⊗Cat {C = A} {D = B} {E = C})
            (⊗Cat {C = A} {D = C} {E = D})
     rF = RightBiasedDoubleApplicationFunctor
            (⊗Cat {C = B} {D = C} {E = D})
            (⊗Cat {C = A} {D = B} {E = D})
    associator-NT : NaturalTransformation lF rF
    associator-NT = record
      { obj = \{ (triple f1 f2 f3) -> ⋆F-assoc-NT f1 f2 f3 }
      ; mor = \{tf1} {tf2} m -> natural-transformation-path (\a ->
          ⋆-left-id >=>
          ⋆-assoc >=>
          ⋆-right (sym (F-⋆ (Triple.c tf2) _ _)) >=>
          sym ⋆-right-id)
      }

    associator-isNI : isNaturalIso _ _ associator-NT
    associator-isNI (triple f1 f2 f3) = record
      { inv = ⋆F-assoc-NT' f1 f2 f3
      ; sec = natural-transformation-path (\_ -> ⋆-right-id)
      ; ret = natural-transformation-path (\_ -> ⋆-right-id)
      }

    associator-NT' : NaturalTransformation rF lF
    associator-NT' = fst (flip-NI (associator-NT , associator-isNI))


private
  module _ {ℓO ℓM : Level}
           {A : PreCategory ℓO ℓM}
           {B : PreCategory ℓO ℓM}
           {C : PreCategory ℓO ℓM}
           {f : Functor A B}
           {g : Functor B C}
           where
    open CategoryHelpers C

    opaque
      triangle-NT :
        (NT-obj associator-NT (triple f (idF B) g)) ⋆NT
        (id-NT f ⋆NTʰ (NT-obj unitorˡ-NT g)) ==
        ((NT-obj unitorʳ-NT f) ⋆NTʰ (id-NT g))
      triangle-NT = natural-transformation-path (\_ -> ⋆-left-id >=> refl)


  module _ {ℓO ℓM : Level}
           {A : PreCategory ℓO ℓM}
           {B : PreCategory ℓO ℓM}
           {C : PreCategory ℓO ℓM}
           {D : PreCategory ℓO ℓM}
           {E : PreCategory ℓO ℓM}
           (f : Functor A B)
           (g : Functor B C)
           (h : Functor C D)
           (i : Functor D E)
    where
    open CategoryHelpers E

    private
     rF = RightBiasedDoubleApplicationFunctor
            (⊗Cat {C = C} {D = D} {E = E})
            (⊗Cat {C = B} {D = C} {E = E})
    opaque
      pentagon-NT :
        (NT-obj associator-NT (triple (f ⋆F g) h i)) ⋆NT
        (NT-obj associator-NT (triple f g (h ⋆F i)))
        ==
        ((NT-obj associator-NT (triple f g h) ⋆NTʰ (id-NT i)) ⋆NT
         (NT-obj associator-NT (triple f (g ⋆F h) i))) ⋆NT
         ((id-NT f) ⋆NTʰ NT-obj associator-NT (triple g h i))
      pentagon-NT = natural-transformation-path (\a ->
        ⋆-left-id >=>
        sym (
          ⋆-left (⋆-right-id >=> ⋆-left-id >=> (F-id i _)) >=>
          ⋆-left-id >=>
          ⋆-left-id >=>
          (F-id (F-obj rF (triple g h i)) _)))

module _ where
  CatC : (ℓO ℓM : Level) -> PreBiCategory (ℓ-suc (ℓ-max ℓO ℓM)) (ℓ-max ℓO ℓM) (ℓ-max ℓO ℓM)
  CatC ℓO ℓM = record
    { Obj = PreCategory ℓO ℓM
    ; Mor = \C D -> FunctorC C D
    ; id₁ = \C -> idF C
    ; ⊗ = ⊗Cat
    ; unitorˡ = \C D -> unitorˡ-NT , unitorˡ-isNI
    ; unitorʳ = \C D -> unitorʳ-NT , unitorʳ-isNI
    ; associator = \A B C D -> associator-NT , associator-isNI
    ; triangle = triangle-NT
    ; pentagon = \{A} {B} {C} {D} {E} {f} {g} {h} {i} -> pentagon-NT f g h i
    }
