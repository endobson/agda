{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation
open import sigma.base
open import cubical using (I)
open import equality-path
open import equivalence
open import hlevel
open import isomorphism

module category.base where

private
  variable
    ℓObj ℓMor : Level

-- TODO try to make ⋆-left-id and others not take in an object

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

  ⋆-cong : {s t u : Obj} {m1 m2 : Mor s t} {m3 m4 : Mor t u} ->
           m1 == m2 -> m3 == m4 -> m1 ⋆ m3 == m2 ⋆ m4
  ⋆-cong p12 p34 i = p12 i ⋆ p34 i

  ⋆-left : {s t u : Obj} {m1 m2 : Mor s t} {m3 : Mor t u} ->
           m1 == m2 -> m1 ⋆ m3 == m2 ⋆ m3
  ⋆-left {m3 = m3} p12 i = p12 i ⋆ m3

  ⋆-right : {s t u : Obj} {m1 : Mor s t} {m2 m3 : Mor t u} ->
           m2 == m3 -> m1 ⋆ m2 == m1 ⋆ m3
  ⋆-right {m1 = m1} p23 i = m1 ⋆ p23 i

  ⋆-assocⁱ : {s t u v : Obj} -> {f : Mor s t} -> {g : Mor t u} -> {h : Mor u v} ->
             (f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
  ⋆-assocⁱ = ⋆-assoc _ _ _

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

record CatIso (C : PreCategory ℓObj ℓMor) (x y : C .Obj) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  constructor cat-iso
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
  _^op .PreCategory.isSet-Mor = C.isSet-Mor


record isIso (C : PreCategory ℓObj ℓMor) {x y : C .Obj} (mor : C [ x , y ]) : Type ℓMor where
  constructor is-iso
  field
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

isProp-isIso : {C : PreCategory ℓObj ℓMor} -> {x y : C .Obj} {mor : C [ x , y ]} ->
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
  ans-ret = isProp->PathP (\i -> (C.isSet-Mor _ _))

  sec-line : I -> Type _
  sec-line i = ip i ⋆⟨ C ⟩ mor == C.id
  ans-sec : PathP sec-line i1.sec i2.sec
  ans-sec = isProp->PathP (\i -> (C.isSet-Mor _ _))

module _ {C : PreCategory ℓObj ℓMor} {x y : C .Obj} where
  ΣIso≃CatIso : Σ (C [ x , y ]) (isIso C) ≃ CatIso C x y
  ΣIso≃CatIso = isoToEquiv i
    where
    i : Iso (Σ (C [ x , y ]) (isIso C)) (CatIso C x y)
    i .Iso.fun (mor , (is-iso inv sec ret)) = (cat-iso mor inv sec ret)
    i .Iso.inv (cat-iso mor inv sec ret) = (mor , (is-iso inv sec ret))
    i .Iso.leftInv _ = refl
    i .Iso.rightInv _ = refl

  cat-iso-path : {i1 i2 : CatIso C x y} ->
    CatIso.mor i1 == CatIso.mor i2 -> i1 == i2
  cat-iso-path {i1} {i2} mor-path =
    sym (eqSec ΣIso≃CatIso i1) >=> cong (eqFun ΣIso≃CatIso) p1 >=> (eqSec ΣIso≃CatIso i2)
    where
    Σi1 = eqInv ΣIso≃CatIso i1
    Σi2 = eqInv ΣIso≃CatIso i2
    p1 : Σi1 == Σi2
    p1 = ΣProp-path (isProp-isIso) mor-path


record isThin (C : PreCategory ℓObj ℓMor) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  field
    isProp-Mor : {x y : C .Obj} -> isProp (C [ x , y ])

-- Functors

record Functor {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
               (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) :
               Type (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD) where
  no-eta-equality
  field
    obj : Obj C -> Obj D
    mor : {x y : Obj C} -> C [ x , y ] -> D [ obj x , obj y ]
    id : (x : Obj C) -> (mor (idᵉ C x)) == (id D)
    ⋆ : {x y z : Obj C} -> (f : C [ x , y ]) -> (g : C [ y , z ]) ->
         mor (f ⋆⟨ C ⟩ g) == (mor f ⋆⟨ D ⟩ mor g)

open Functor public renaming
  ( obj to F-obj
  ; mor to F-mor
  ; id to F-id
  ; ⋆ to F-⋆
  )

-- Add an alias for Diagrams.
Diagram = Functor

-- Identity Functor

idF : {ℓObjC ℓMorC : Level} (C : PreCategory ℓObjC ℓMorC) -> Functor C C
idF _ .F-obj x = x
idF _ .F-mor f = f
idF _ .F-id _ = refl
idF _ .F-⋆ f g = refl

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
  (nt1 nt2 : NaturalTransformation F G) where

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
