{-# OPTIONS --cubical --safe --exact-split #-}

module category2.base where

open import base
open import cubical
open import equality-path
open import hlevel.base

module _ {ℓO ℓM : Level} {Obj : Type ℓO} (Mor : Obj -> Obj -> Type ℓM) where
  record CategoryStr : Type (ℓ-max ℓO ℓM) where
    field
      id : {o : Obj} -> Mor o o

    idᵉ : (o : Obj) -> Mor o o
    idᵉ _ = id

    field
      _⋆_ : {s t u : Obj} -> Mor s t -> Mor t u -> Mor s u
      -- Maybe make these implicit since many times they can be infered
      ⋆-left-idᵉ : {s t : Obj} -> (f : Mor s t) -> id ⋆ f == f
      ⋆-right-idᵉ : {s t : Obj} -> (f : Mor s t) -> f ⋆ id == f
      ⋆-assocᵉ : {s t u v : Obj} -> (f : Mor s t) -> (g : Mor t u) -> (h : Mor u v) ->
                 (f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
      isSet-Mor : {s t : Obj} -> isSet (Mor s t)

    infixl 15 _⋆_
    infixr 16 _∘_


    ⋆-left-id : {s t : Obj} -> {f : Mor s t} -> id ⋆ f == f
    ⋆-left-id = ⋆-left-idᵉ _
    ⋆-right-id : {s t : Obj} -> {f : Mor s t} -> f ⋆ id == f
    ⋆-right-id = ⋆-right-idᵉ _
    ⋆-assoc : {s t u v : Obj} -> {f : Mor s t} -> {g : Mor t u} -> {h : Mor u v} ->
              (f ⋆ g) ⋆ h == f ⋆ (g ⋆ h)
    ⋆-assoc = ⋆-assocᵉ _ _ _


    _∘_ : {s t u : Obj} -> Mor t u -> Mor s t -> Mor s u
    f ∘ g = g ⋆ f

    ∘-left-id : {s t : Obj} -> {f : Mor s t} -> id ∘ f == f
    ∘-left-id = ⋆-right-id
    ∘-right-id : {s t : Obj} -> {f : Mor s t} -> f ∘ id == f
    ∘-right-id = ⋆-left-id
    ∘-assoc : {s t u v : Obj} -> {f : Mor u v} -> {g : Mor t u} -> {h : Mor s t} ->
              (f ∘ g) ∘ h == f ∘ (g ∘ h)
    ∘-assoc {f = f} {g} {h} i = ⋆-assocᵉ h g f (~ i)

module _ {ℓO ℓM : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         {{CS : CategoryStr M}} where
  open CategoryStr CS public hiding (isSet-Mor)


  ⋆-left : {s t u : O} {m₁ m₂ : M s t} {m₃ : M t u} ->
           m₁ == m₂ -> m₁ ⋆ m₃ == m₂ ⋆ m₃
  ⋆-left {m₃ = m₃} p₁₂ i = p₁₂ i ⋆ m₃

  ⋆-right : {s t u : O} {m₁ : M s t} {m₃ m₂ : M t u} ->
           m₂ == m₃ -> m₁ ⋆ m₂ == m₁ ⋆ m₃
  ⋆-right {m₁ = m₁} p₂₃ i = m₁ ⋆ p₂₃ i

  opaque
    isSet-Mor : {o₁ o₂ : O} -> isSet (M o₁ o₂)
    isSet-Mor = CategoryStr.isSet-Mor CS



record Category (ℓObj ℓMor : Level) : Type (ℓ-suc (ℓ-max ℓObj ℓMor)) where
  constructor category
  field
    Obj : Type ℓObj
    Mor : Obj -> Obj -> Type ℓMor
    Str : CategoryStr Mor

open Category public using (Obj)

_→[_,_] : {ℓO ℓM : Level} (C : Category ℓO ℓM) (x y : Obj C) -> Type ℓM
_→[_,_] C x y = Category.Mor C x y


module _ {ℓO ℓM : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         (CS : CategoryStr M) where
  Category▪ : Category ℓO ℓM
  Category▪ = record { Obj = O ; Mor = M ; Str = CS }





module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  (C₁@(category O₁ M₁ _) : Category ℓO₁ ℓM₁)
  (C₂@(category O₂ M₂ _) : Category ℓO₂ ℓM₂)
  where
  private
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  record Functor : Type (ℓ-max* 4 ℓO₁ ℓO₂ ℓM₁ ℓM₂) where
    field
      obj : Obj C₁ -> Obj C₂
      mor : {x y : Obj C₁} -> M₁ x y -> M₂ (obj x) (obj y)
      preserves-idᵉ : (x : Obj C₁) -> (mor (idᵉ x)) == idᵉ (obj x)
      preserves-⋆ᵉ : {x y z : Obj C₁} -> (f : M₁ x y) -> (g : M₁ y z) ->
        mor (f ⋆ g) == mor f ⋆ mor g

    preserves-id : {x : Obj C₁} -> (mor (idᵉ x)) == idᵉ (obj x)
    preserves-id = preserves-idᵉ _

    preserves-⋆ : {x y z : Obj C₁} -> {f : M₁ x y} -> {g : M₁ y z} ->
      mor (f ⋆ g) == mor f ⋆ mor g
    preserves-⋆ = preserves-⋆ᵉ _ _

  record Functorᵒᵖ : Type (ℓ-max* 4 ℓO₁ ℓO₂ ℓM₁ ℓM₂) where
    field
      obj : Obj C₁ -> Obj C₂
      mor : {x y : Obj C₁} -> M₁ x y -> M₂ (obj y) (obj x)
      preserves-idᵉ : (x : Obj C₁) -> (mor (idᵉ x)) == idᵉ (obj x)
      preserves-⋆ᵉ : {x y z : Obj C₁} -> (f : M₁ x y) -> (g : M₁ y z) ->
        mor (f ⋆ g) == mor g ⋆ mor f

    preserves-id : {x : Obj C₁} -> (mor (idᵉ x)) == idᵉ (obj x)
    preserves-id = preserves-idᵉ _

    preserves-⋆ : {x y z : Obj C₁} -> {f : M₁ x y} -> {g : M₁ y z} ->
      mor (f ⋆ g) == mor g ⋆ mor f
    preserves-⋆ = preserves-⋆ᵉ _ _


module _
  {ℓO₁ ℓM₁ ℓO₂ ℓM₂ ℓO₃ ℓM₃ : Level}
  {C₁ : Category ℓO₁ ℓM₁} {C₂ : Category ℓO₂ ℓM₂} {C₃ : Category ℓO₃ ℓM₃}
  (F : Functor C₁ C₂) (G : Functor C₂ C₃)
  where

  _⋆F_ : Functor C₁ C₃
  _⋆F_ = record
    { obj = \o -> G.obj (F.obj o)
    ; mor = \m -> G.mor (F.mor m)
    ; preserves-idᵉ = \m -> cong G.mor F.preserves-id >=> G.preserves-id
    ; preserves-⋆ᵉ = \f g -> cong G.mor F.preserves-⋆ >=> G.preserves-⋆
    }
    where
    module F = Functor F
    module G = Functor G
