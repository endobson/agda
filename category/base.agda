{-# OPTIONS --cubical --safe --exact-split #-}

module category.base where

open import base
open import cubical using (isEquiv ; I)
open import equality-path
open import hlevel

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

idᵉ : (C : PreCategory ℓObj ℓMor) -> (x : Obj C) -> C [ x , x ]
idᵉ C _ = id C

record isCategory (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isSet-Mor : {x y : C .Obj} -> isSet (C [ x , y ])

isSet-Mor : {C : PreCategory ℓObj ℓMor} {{isCat : isCategory C}} ->
            {x y : C .Obj} -> isSet (C [ x , y ])
isSet-Mor {{isCat}} = isCategory.isSet-Mor isCat

record CatIso (C : PreCategory ℓObj ℓMor) (x y : C .Obj) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

idCatIso : (C : PreCategory ℓObj ℓMor) (x : C .Obj) -> CatIso C x x
idCatIso C x = record
  { mor = C .id
  ; inv = C .id
  ; sec = PreCategory.⋆-left-id C _
  ; ret = PreCategory.⋆-left-id C _
  }

pathToCatIso : (C : PreCategory ℓObj ℓMor) (x y : C .Obj) -> x == y -> CatIso C x y
pathToCatIso C x _ = J (\ y _ -> CatIso C x y) (idCatIso C x)

pathToCatIso-refl : (C : PreCategory ℓObj ℓMor) (x : C .Obj) ->
                    pathToCatIso C x x refl == idCatIso C x
pathToCatIso-refl C x = JRefl (\ y _ -> CatIso C x y) (idCatIso C x)

record isUnivalent (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isEquiv-pathToCatIso : (x y : C .Obj) -> isEquiv (pathToCatIso C x y)

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


record isIso (C : PreCategory ℓObj ℓMor) {x y : C .Obj} (mor : C [ x , y ]) : Type ℓMor where
  constructor is-iso
  field
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

isProp-isIso : {C : PreCategory ℓObj ℓMor} -> {{isCategory C}} -> {x y : C .Obj} {mor : C [ x , y ]} ->
               isProp (isIso C mor)
isProp-isIso {C = C} {x} {y} {mor} i1 i2 = (\i -> record
    { inv = ip i
    ; sec = ans-sec i
    ; ret = ans-ret i
    })
  where
  module C = PreCategory C
  module i1 = isIso i1
  module i2 = isIso i2

  ip : i1.inv == i2.inv
  ip = sym (C.⋆-left-id _) >=>
       cong (C._⋆ i1.inv) (sym i2.sec) >=>
       C.⋆-assoc i2.inv mor i1.inv >=>
       cong (i2.inv C.⋆_) i1.ret >=>
       (C.⋆-right-id i2.inv)

  ret-line : I -> Type _
  ret-line i = mor ⋆⟨ C ⟩ ip i == C.id
  ans-ret : PathP ret-line i1.ret i2.ret
  ans-ret = isProp->PathP (\i -> (isSet-Mor _ _)) _ _

  sec-line : I -> Type _
  sec-line i = ip i ⋆⟨ C ⟩ mor == C.id
  ans-sec : PathP sec-line i1.sec i2.sec
  ans-sec = isProp->PathP (\i -> (isSet-Mor _ _)) _ _

record isThin (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isProp-Mor : {x y : C .Obj} -> isProp (C [ x , y ])

-- Functors

record Functor {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
               (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) :
               Type (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD) where
  no-eta-equality
  field
    F-obj : Obj C -> Obj D
    F-mor : {x y : Obj C} -> C [ x , y ] -> D [ F-obj x , F-obj y ]
    F-id : (x : Obj C) -> (F-mor (idᵉ C x)) == (id D)
    F-⋆ : {x y z : Obj C} -> (f : C [ x , y ]) -> (g : C [ y , z ]) ->
          F-mor (f ⋆⟨ C ⟩ g) == (F-mor f ⋆⟨ D ⟩ F-mor g)

open Functor
