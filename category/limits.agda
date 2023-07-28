{-# OPTIONS --cubical --safe --exact-split #-}

module category.limits where

open import base
open import boolean
open import hlevel
open import category.base
open import category.instances.quiver
open import category.instances.free
open import category.set
open import truncation
open import relation

private
  Diagram = Functor

record Cone {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
            (D : Diagram J C) (v : Obj C) :
            Type (ℓ-max* 4 ℓOJ ℓMJ ℓOC ℓMC) where
  private
    module D = Functor D

  field
    component : (j : Obj J) -> C [ v , D.obj j ]
    component-compose :
      {j1 j2 : Obj J} -> (f : J [ j1 , j2 ]) ->
      component j1 ⋆⟨ C ⟩ (D.mor f) == component j2


ConeFactorsThrough :
  {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
  {D : Diagram J C} {v1 v2 : Obj C}
  (cone1 : Cone D v1) (cone2 : Cone D v2) (f : C [ v1 , v2 ]) ->
  Type (ℓ-max ℓOJ ℓMC)
ConeFactorsThrough {C = C} c1 c2 f = ∀ j -> c1.component j == f ⋆⟨ C ⟩ c2.component j
  where
  module c1 = Cone c1
  module c2 = Cone c2

isProp-ConeFactorsThrough :
  {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
  {D : Diagram J C} {v1 v2 : Obj C}
  (cone1 : Cone D v1) (cone2 : Cone D v2) {f : C [ v1 , v2 ]} ->
  isProp (ConeFactorsThrough cone1 cone2 f)
isProp-ConeFactorsThrough {C = C} _ _ = isPropΠ (\_ -> isSet-Mor C _ _)


isLimitCone : {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
              (D : Diagram J C) (v : Obj C) (cone : Cone D v) -> Type (ℓ-max* 4 ℓOJ ℓMJ ℓOC ℓMC)
isLimitCone {C = C} J v cone =
  ∀ v2 cone2 -> ∃![ f ∈ C [ v2 , v ] ] (ConeFactorsThrough cone2 cone f)

record LimCone {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
               (D : Diagram J C) : Type (ℓ-max* 4 ℓOJ ℓMJ ℓOC ℓMC) where
  field
    limit : Obj C
    cone : Cone D limit
    isLimit : isLimitCone D limit cone

hasLimitsOfShape : {ℓOJ ℓMJ ℓOC ℓMC : Level} (J : PreCategory ℓOJ ℓMJ) (C : PreCategory ℓOC ℓMC) -> Type _
hasLimitsOfShape J C = (D : Diagram J C) -> LimCone D
