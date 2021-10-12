{-# OPTIONS --cubical --safe --exact-split #-}

module category.base where

open import base
open import cubical
open import hlevel
open import equality-path using (J)

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

  _∘_ : {s t u : Obj} -> Mor t u -> Mor s t -> Mor s u
  f ∘ g = g ⋆ f

  ∘-left-id : {s t : Obj} -> (f : Mor s t) -> id ∘ f == f
  ∘-left-id = ⋆-right-id
  ∘-right-id : {s t : Obj} -> (f : Mor s t) -> f ∘ id == f
  ∘-right-id = ⋆-left-id
  ∘-assoc : {s t u v : Obj} -> (f : Mor u v) -> (g : Mor t u) -> (h : Mor s t) ->
            (f ∘ g) ∘ h == f ∘ (g ∘ h)
  ∘-assoc f g h i = ⋆-assoc h g f (~ i)

open PreCategory public using (Obj ; id)

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

record isCategory (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isSet-Mor : (x y : C .Obj) -> isSet (C [ x , y ])

record CatIso (C : PreCategory ℓObj ℓMor) (x y : C .Obj) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

pathToIso : (C : PreCategory ℓObj ℓMor) (x y : C .Obj) -> x == y -> CatIso C x y
pathToIso C _ _ = J (\ y _ -> CatIso C _ y) (record
  { mor = C .id
  ; inv = C .id
  ; sec = PreCategory.⋆-left-id C _
  ; ret = PreCategory.⋆-left-id C _
  })

record isUnivalent (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isEquiv-pathToIso : (x y : C .Obj) -> isEquiv (pathToIso C x y)


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
