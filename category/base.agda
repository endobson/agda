{-# OPTIONS --cubical --safe --exact-split #-}

module category.base where

open import base
open import cubical using (I)
open import equality-path
open import equivalence
open import hlevel
open import isomorphism
open import relation
open import sigma.base

private
  variable
    ℓObj ℓMor : Level

record PreCategory (ℓObj ℓMor : Level) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    Obj : Type ℓObj
    Mor : (s t : Obj) -> Type ℓMor
    id : {s : Obj} -> Mor s s
    _⋆_ : {s t u : Obj} -> Mor s t -> Mor t u -> Mor s u
    ⋆-left-id : {s t : Obj} -> (f : Mor s t) -> id ⋆ f == f
    ⋆-right-id : {s t : Obj} -> (f : Mor s t) -> f ⋆ id == f
    ⋆-assoc : {s t u v : Obj} -> (f : Mor s t) -> (g : Mor t u) -> (h : Mor u v) ->
              (f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
    isSet-Mor : {s t : Obj} -> isSet (Mor s t)

  infixl 15 _⋆_
  infixr 16 _∘_

  ⋆-id² : {s : Obj} -> Path (Mor s s) (id ⋆ id) id
  ⋆-id² = ⋆-left-id id

  _∘_ : {s t u : Obj} -> Mor t u -> Mor s t -> Mor s u
  f ∘ g = g ⋆ f

  ∘-left-id : {s t : Obj} -> (f : Mor s t) -> id ∘ f == f
  ∘-left-id = ⋆-right-id
  ∘-right-id : {s t : Obj} -> (f : Mor s t) -> f ∘ id == f
  ∘-right-id = ⋆-left-id
  ∘-assoc : {s t u v : Obj} -> (f : Mor u v) -> (g : Mor t u) -> (h : Mor s t) ->
            (f ∘ g) ∘ h == f ∘ (g ∘ h)
  ∘-assoc f g h i = ⋆-assoc h g f (~ i)


open PreCategory public using (Obj ; id ; isSet-Mor)

_[_,_] : (C : PreCategory ℓObj ℓMor) -> (x y : C .Obj) -> Type ℓMor
_[_,_] = PreCategory.Mor

seq' : (C : PreCategory ℓObj ℓMor) {x y z : C .Obj} (f : C [ x , y ]) (g : C [ y , z ]) -> C [ x , z ]
seq' = PreCategory._⋆_

comp' : (C : PreCategory ℓObj ℓMor) {x y z : C .Obj} (f : C [ y , z ]) (g : C [ x , y ]) -> C [ x , z ]
comp' = PreCategory._∘_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f

idᵉ : (C : PreCategory ℓObj ℓMor) -> (x : Obj C) -> C [ x , x ]
idᵉ C _ = id C

module CategoryHelpers {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  private
    module C = PreCategory C
  open C
    using (_⋆_ ; ⋆-id²)
    renaming ( ⋆-left-id to ⋆-left-idᵉ
             ; ⋆-right-id to ⋆-right-idᵉ )
    public

  ⋆-left-id : {s t : Obj C} {f : C [ s , t ]} -> id C ⋆ f == f
  ⋆-left-id = C.⋆-left-id _
  ⋆-right-id : {s t : Obj C} {f : C [ s , t ]} -> f ⋆ id C == f
  ⋆-right-id = C.⋆-right-id _

  ⋆-assoc : {s t u v : Obj C} {f : C [ s , t ]} {g : C [ t , u ]} {h : C [ u , v ]} ->
            (f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
  ⋆-assoc = C.⋆-assoc _ _ _

  ⋆-cong : {s t u : Obj C} {m1 m2 : C [ s , t ]} {m3 m4 : C [ t , u ]} ->
           m1 == m2 -> m3 == m4 -> m1 ⋆ m3 == m2 ⋆ m4
  ⋆-cong p12 p34 i = p12 i ⋆ p34 i

  ⋆-left : {s t u : Obj C} {m1 m2 : C [ s , t ]} {m3 : C [ t , u ]} ->
           m1 == m2 -> m1 ⋆ m3 == m2 ⋆ m3
  ⋆-left {m3 = m3} p12 i = p12 i ⋆ m3

  ⋆-right : {s t u : Obj C} {m1 : C [ s , t ]} {m2 m3 : C [ t , u ]} ->
           m2 == m3 -> m1 ⋆ m2 == m1 ⋆ m3
  ⋆-right {m1 = m1} p23 i = m1 ⋆ p23 i

module _ (C : PreCategory ℓObj ℓMor) where
  private
    module C = PreCategory C

  _^op : PreCategory ℓObj ℓMor
  _^op .PreCategory.Obj = C.Obj
  _^op .PreCategory.Mor x y = C.Mor y x
  _^op .PreCategory.id = C.id
  _^op .PreCategory._⋆_ = C._∘_
  _^op .PreCategory.⋆-left-id = C.∘-left-id
  _^op .PreCategory.⋆-right-id = C.∘-right-id
  _^op .PreCategory.⋆-assoc = C.∘-assoc
  _^op .PreCategory.isSet-Mor = C.isSet-Mor


record isThin (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isProp-Mor : {x y : C .Obj} -> isProp (C [ x , y ])

-- Helpers for defining new categorys

record CategorySorts (ℓObj ℓMor : Level) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    Obj : Type ℓObj
    Mor : Rel Obj ℓMor

record CategoryOps {ℓObj ℓMor : Level} (S : CategorySorts ℓObj ℓMor) : Type (ℓ-max ℓObj ℓMor) where
  private
    module S = CategorySorts S

  field
    id : {s : S.Obj} -> S.Mor s s
    _⋆_ : {s t u : S.Obj} -> S.Mor s t -> S.Mor t u -> S.Mor s u

record CategoryLaws {ℓObj ℓMor : Level} {S : CategorySorts ℓObj ℓMor}
                    (O : CategoryOps S) : Type (ℓ-max ℓObj ℓMor) where
  private
    module S = CategorySorts S
    module O = CategoryOps O

  field
    ⋆-left-id : {s t : S.Obj} -> (f : S.Mor s t) -> O.id O.⋆ f == f
    ⋆-right-id : {s t : S.Obj} -> (f : S.Mor s t) -> f O.⋆ O.id == f
    ⋆-assoc : {s t u v : S.Obj} -> (f : S.Mor s t) -> (g : S.Mor t u) -> (h : S.Mor u v) ->
              (f O.⋆ g) O.⋆ h == f O.⋆ (g O.⋆ h)
    isSet-Mor : {s t : S.Obj} -> isSet (S.Mor s t)

Laws->Category :
  {ℓObj ℓMor : Level} {S : CategorySorts ℓObj ℓMor}
  {O : CategoryOps S} -> (CategoryLaws O) -> PreCategory ℓObj ℓMor
Laws->Category {S = S} {O = O} L .PreCategory.Obj = CategorySorts.Obj S
Laws->Category {S = S} {O = O} L .PreCategory.Mor = CategorySorts.Mor S
Laws->Category {S = S} {O = O} L .PreCategory.id = CategoryOps.id O
Laws->Category {S = S} {O = O} L .PreCategory._⋆_ = CategoryOps._⋆_ O
Laws->Category {S = S} {O = O} L .PreCategory.⋆-left-id = CategoryLaws.⋆-left-id L
Laws->Category {S = S} {O = O} L .PreCategory.⋆-right-id = CategoryLaws.⋆-right-id L
Laws->Category {S = S} {O = O} L .PreCategory.⋆-assoc = CategoryLaws.⋆-assoc L
Laws->Category {S = S} {O = O} L .PreCategory.isSet-Mor = CategoryLaws.isSet-Mor L
