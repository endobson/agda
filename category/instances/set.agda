{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.set where

open import base
open import category.base
open import category.object.product
open import category.object.terminal
open import category.monoidal.base
open import category.monoidal.cartesian
open import category.monoidal.constructions.cartesian
open import category.univalent
open import cubical
open import cubical using (I)
open import equality-path
open import equality.identity-system
open import funext
open import hlevel
open import isomorphism
open import sigma.base
open import truncation
open import univalence

private
  variable
    ℓ : Level

record SetFunction (x y : hSet ℓ) : Type ℓ where
  constructor set-function
  field
    f : ⟨ x ⟩ -> ⟨ y ⟩

isSet-SetFunction : {x y : hSet ℓ} -> isSet (SetFunction x y)
isSet-SetFunction {y = y} =
  isSet-Retract SetFunction.f set-function (\_ -> refl) (isSetΠ (\_ -> snd y))


SetC : (ℓ : Level) -> PreCategory (ℓ-suc ℓ) ℓ
SetC ℓ .PreCategory.Obj = hSet ℓ
SetC ℓ .PreCategory.Mor x y = SetFunction x y
SetC ℓ .PreCategory.id = (set-function \x -> x)
SetC ℓ .PreCategory._⋆_ (set-function f) (set-function g) = (set-function (\x -> g (f x)))
SetC ℓ .PreCategory.⋆-left-id f = refl
SetC ℓ .PreCategory.⋆-right-id f = refl
SetC ℓ .PreCategory.⋆-assoc f g h = refl
SetC ℓ .PreCategory.isSet-Mor = isSet-SetFunction

private
  CatIso->Iso : {x y : hSet ℓ} -> CatIso (SetC ℓ) x y -> Iso ⟨ x ⟩ ⟨ y ⟩
  CatIso->Iso ciso .Iso.fun = SetFunction.f (CatIso.mor ciso)
  CatIso->Iso ciso .Iso.inv = SetFunction.f (CatIso.inv ciso)
  CatIso->Iso ciso .Iso.leftInv x i = SetFunction.f (CatIso.ret ciso i) x
  CatIso->Iso ciso .Iso.rightInv x i = SetFunction.f (CatIso.sec ciso i) x

  Iso->CatIso : {x y : hSet ℓ} -> Iso ⟨ x ⟩ ⟨ y ⟩ -> CatIso (SetC ℓ) x y
  Iso->CatIso i .CatIso.mor .SetFunction.f = (Iso.fun i)
  Iso->CatIso i .CatIso.inv .SetFunction.f = (Iso.inv i)
  Iso->CatIso i .CatIso.ret x .SetFunction.f j = (Iso.leftInv i j) x
  Iso->CatIso i .CatIso.sec x .SetFunction.f j = (Iso.rightInv i j) x

module _ {ℓ : Level} where
  open isIdentitySystem

  isUnivalent'-SetC : isUnivalent' (SetC ℓ)
  isUnivalent'-SetC .to-path c = isIdentitySystem-Iso .to-path (CatIso->Iso c)
  isUnivalent'-SetC .to-path-over {a} {b} c i =
    Iso->CatIso (isIdentitySystem-Iso .to-path-over {a} {b} (CatIso->Iso c) i)

hasProducts-SetC : {ℓ : Level} -> hasProducts (SetC ℓ)
hasProducts-SetC {ℓ} sA@(A , hA) sB@(B , hB) = record
  { obj = obj
  ; π₁ = π₁
  ; π₂ = π₂
  ; universal = universal
  }
  where
  C = SetC ℓ
  obj = (A × B) , isSet× hA hB
  π₁ = set-function proj₁
  π₂ = set-function proj₂
  universal : ∀ {sX} (f : SetFunction sX sA) (g : SetFunction sX sB) ->
              ∃![ h ∈ (SetFunction sX obj) ] (h ⋆⟨ C ⟩ π₁ == f × h ⋆⟨ C ⟩ π₂ == g)
  universal (set-function f) (set-function g) =
    (set-function (\x -> f x , g x) , (refl , refl)) ,
    (\(h2 , p1 , p2) i ->
      (set-function (\x -> SetFunction.f (p1 (~ i)) x , SetFunction.f (p2 (~ i)) x)) ,
      (\j -> set-function (\x -> SetFunction.f (p1 ((~ i) ∨ j)) x)) ,
      (\j -> set-function (\x -> SetFunction.f (p2 ((~ i) ∨ j)) x)))

Terminal-SetC : {ℓ : Level} -> Terminal (SetC ℓ)
Terminal-SetC {ℓ} = record
  { obj = T
  ; universal = universal
  }
  where
  C = SetC ℓ
  T : Obj C
  T = Lift ℓ Top , isSet-Lift (isProp->isSet isPropTop)
  universal : (S : Obj C) -> isContr (C [ S , T ])
  universal (S , isSet-S)  =
    set-function (\_ -> lift tt) , (\f i -> (set-function (\x -> lift tt)))

Set×-MC : (ℓ : Level) -> MonoidalCategory (ℓ-suc ℓ) ℓ
Set×-MC ℓ = SetC ℓ , CartesianMonoidalStr hasProducts-SetC Terminal-SetC

Set×-CMC : (ℓ : Level) -> CartesianMonoidalCategory (ℓ-suc ℓ) ℓ
Set×-CMC ℓ = Set×-MC ℓ , isCartesian-CartesianMonoidalStr hasProducts-SetC Terminal-SetC
