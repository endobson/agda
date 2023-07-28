{-# OPTIONS --cubical --safe --exact-split #-}

module category.set where

open import base
open import category.base
open import cubical using (I)
open import equality-path
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


  CatIso->Iso-id : (x : hSet ℓ) -> CatIso->Iso (idCatIso (SetC ℓ) x) == id-iso
  CatIso->Iso-id (X , isSet-X) = isSet-iso-path isSet-X isSet-X refl

  CatIso->Iso-path : (x : hSet ℓ) -> isoToPath (CatIso->Iso (idCatIso (SetC ℓ) x)) == refl
  CatIso->Iso-path x = cong isoToPath (CatIso->Iso-id x) >=> isoToPath-id-iso

  CatIso-mor-path : {ℓObj ℓMor : Level} (C : PreCategory ℓObj ℓMor) ->
                    (x y : C .Obj) -> (c1 c2 : CatIso C x y) ->
                    CatIso.mor c1 == CatIso.mor c2 -> c1 == c2
  CatIso-mor-path {ℓMor = ℓ} C x y c1 c2 mp = (\i -> record
    { mor = mp i
    ; inv = ip i
    ; sec = ans-sec i
    ; ret = ans-ret i
    })
    where
    module C = PreCategory C
    module c1 = CatIso c1
    module c2 = CatIso c2

    ip : c1.inv == c2.inv
    ip = sym (C.⋆-left-id _) >=>
         cong (C._⋆ c1.inv) (sym c2.sec) >=>
         C.⋆-assoc c2.inv c2.mor c1.inv >=>
         cong (c2.inv C.⋆_) (cong (C._⋆ c1.inv) (sym mp) >=> c1.ret) >=>
         (C.⋆-right-id c2.inv)

    ret-line : I -> Type ℓ
    ret-line i = mp i ⋆⟨ C ⟩ ip i == C.id
    ans-ret : PathP ret-line c1.ret c2.ret
    ans-ret = isProp->PathP (\i -> (C.isSet-Mor _ _))

    sec-line : I -> Type ℓ
    sec-line i = ip i ⋆⟨ C ⟩ mp i == C.id
    ans-sec : PathP sec-line c1.sec c2.sec
    ans-sec = isProp->PathP (\i -> (C.isSet-Mor _ _))



  module _ {ℓ : Level} where
    private
      forward : (x y : hSet ℓ) -> (x == y) -> (CatIso (SetC ℓ) x y)
      forward = pathToCatIso (SetC _)
      backward : (x y : hSet ℓ) -> (CatIso (SetC ℓ) x y) -> (x == y)
      backward _ _ ciso = ΣProp-path isProp-isSet (isoToPath (CatIso->Iso ciso))

      forward-refl : (x : hSet ℓ) -> forward x x refl == idCatIso (SetC ℓ) x
      forward-refl = pathToCatIso-refl (SetC _)

      forward-mor : (x y : hSet ℓ) -> (p : x == y) ->
        CatIso.mor (forward x y p) == set-function (transport (cong fst p))
      forward-mor x y = J P v
        where
        P : (y : hSet ℓ) -> x == y -> Type ℓ
        P y p = CatIso.mor (forward x y p) == set-function (transport (cong fst p))
        v : P x refl
        v = cong CatIso.mor (forward-refl x) >=> cong set-function (funExt (\e -> sym (transportRefl e)))


    module _ {x y : hSet ℓ} where
      Iso-pathToCatIso : Iso (x == y) (CatIso (SetC ℓ) x y)
      Iso-pathToCatIso .Iso.fun = forward _ _
      Iso-pathToCatIso .Iso.inv = backward _ _
      Iso-pathToCatIso .Iso.leftInv = J P v
        where
        P : (y : hSet ℓ) -> x == y -> Type (ℓ-suc ℓ)
        P y p = (backward x y (forward x y p)) == p
        v : P x refl
        v = cong (backward x x) (forward-refl x) >=>
            cong (ΣProp-path isProp-isSet) (CatIso->Iso-path x) >=>
            ΣProp-path-refl isProp-isSet
      Iso-pathToCatIso .Iso.rightInv c =
        CatIso-mor-path (SetC ℓ) x y _ _
          (forward-mor x y (backward x y c) >=>
           (cong set-function (transport-isoToPath (CatIso->Iso c))))

abstract
  instance
    isUnivalent-SetC : isUnivalent (SetC ℓ)
    isUnivalent-SetC .isUnivalent.isEquiv-pathToCatIso x y = isoToIsEquiv Iso-pathToCatIso
