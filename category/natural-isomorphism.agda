{-# OPTIONS --cubical --safe --exact-split #-}

module category.natural-isomorphism where

open import base
open import category.base
open import category.constructions.functor-cat
open import category.functor
open import category.isomorphism
open import category.natural-transformation
open import equality-path
open import equivalence
open import hlevel.base
open import isomorphism

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  (F G : Functor C D) where

  isNaturalIso : NaturalTransformation F G -> Type _
  isNaturalIso nt = ∀ c -> isIso D (NT-obj nt c)

  isProp-isNaturalIso : {nt : NaturalTransformation F G} -> isProp (isNaturalIso nt)
  isProp-isNaturalIso = isPropΠ (\_ -> isProp-isIso)

  NaturalIsomorphism : Type _
  NaturalIsomorphism = Σ (NaturalTransformation F G) isNaturalIso

  isNaturalIso' : NaturalTransformation F G -> Type _
  isNaturalIso' nt = isIso (FunctorC C D) nt

  module _ {nt : NaturalTransformation F G} where
    isNaturalIso'->isNaturalIso : isNaturalIso' nt -> isNaturalIso nt
    isNaturalIso'->isNaturalIso (record { inv = inv ; sec = sec ; ret = ret }) c = record
      { inv = NT-obj inv c
      ; sec = \i -> NT-obj (sec i) c
      ; ret = \i -> NT-obj (ret i) c
      }

    isNaturalIso->isNaturalIso' : isNaturalIso nt -> isNaturalIso' nt
    isNaturalIso->isNaturalIso' isos = record
      { inv = inv
      ; sec = natural-transformation-path (\c -> isIso.sec (isos c))
      ; ret = natural-transformation-path (\c -> isIso.ret (isos c))
      }
      where
      inv : NaturalTransformation G F
      inv = record
        { obj = \c -> isIso.inv (isos c)
        ; mor = mor
        }
        where
        open CategoryHelpers D
        mor : {c1 c2 : Obj C} -> (m : C [ c1 , c2 ]) ->
              isIso.inv (isos c1) ⋆ F-mor F m == F-mor G m ⋆ isIso.inv (isos c2)
        mor {c1} {c2} m =
          sym ⋆-right-id >=>
          ⋆-right (sym (isIso.ret (isos c2))) >=>
          ⋆-assoc >=>
          ⋆-right (sym ⋆-assoc >=> ⋆-left (sym (NT-mor nt m)) >=> ⋆-assoc) >=>
          sym ⋆-assoc >=>
          ⋆-left (isIso.sec (isos c1)) >=>
          ⋆-left-id

    isNaturalIso'≃isNaturalIso : isNaturalIso' nt ≃ isNaturalIso nt
    isNaturalIso'≃isNaturalIso =
      isoToEquiv (isProp->iso isNaturalIso'->isNaturalIso isNaturalIso->isNaturalIso'
                   isProp-isIso
                   (isPropΠ (\_ -> isProp-isIso)))
