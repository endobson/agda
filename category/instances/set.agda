{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.set where

open import base
open import category.base
open import category.univalent
open import cubical using (I)
open import equality-path
open import equality.identity-system
open import funext
open import hlevel
open import isomorphism
open import sigma.base
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
