{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.discrete where

open import base
open import category.base
open import equality-path
open import hlevel
open import isomorphism

private
  variable
    ℓObj ℓMor : Level

module _ {D : Type ℓObj} (isSet-D : isSet D) where
  DiscreteC : PreCategory ℓObj ℓObj
  DiscreteC .PreCategory.Obj = D
  DiscreteC .PreCategory.Mor x y = x == y
  DiscreteC .PreCategory.id = refl
  DiscreteC .PreCategory._⋆_ = _>=>_
  DiscreteC .PreCategory.⋆-left-id f = isSet-D _ _ _ _
  DiscreteC .PreCategory.⋆-right-id f = isSet-D _ _ _ _
  DiscreteC .PreCategory.⋆-assoc f g h = isSet-D _ _ _ _
  DiscreteC .PreCategory.isSet-Mor = isProp->isSet (isSet-D _ _)

  isThin-DiscreteC : isThin DiscreteC
  isThin-DiscreteC .isThin.isProp-Mor = isSet-D _ _


  isUnivalent-DiscreteC : isUnivalent DiscreteC
  isUnivalent-DiscreteC .isUnivalent.isEquiv-pathToCatIso x y =
    isoToIsEquiv Iso-pathToCatIso
    where
    isProp-CatIso : isProp (CatIso DiscreteC x y)
    isProp-CatIso c1 c2 = (\i -> record
      { mor = mor-path i
      ; inv = inv-path i
      ; sec = sec-path i
      ; ret = ret-path i
      })
      where
      mor-path : (CatIso.mor c1) == (CatIso.mor c2)
      mor-path i = isSet-D x y (CatIso.mor c1) (CatIso.mor c2) i
      inv-path : (CatIso.inv c1) == (CatIso.inv c2)
      inv-path i = isSet-D y x (CatIso.inv c1) (CatIso.inv c2) i
      sec-path : PathP (\i -> inv-path i ⋆⟨ DiscreteC ⟩ mor-path i == refl)
                       (CatIso.sec c1) (CatIso.sec c2)
      sec-path = isProp->PathP (\i -> isProp->isSet (isSet-D _ _) _ _)
      ret-path : PathP (\i -> mor-path i ⋆⟨ DiscreteC ⟩ inv-path i == refl)
                       (CatIso.ret c1) (CatIso.ret c2)
      ret-path = isProp->PathP (\i -> isProp->isSet (isSet-D _ _) _ _)


    Iso-pathToCatIso : Iso (x == y) (CatIso DiscreteC x y)
    Iso-pathToCatIso .Iso.fun = pathToCatIso DiscreteC x y
    Iso-pathToCatIso .Iso.inv c = CatIso.mor c
    Iso-pathToCatIso .Iso.leftInv _ = isSet-D _ _ _ _
    Iso-pathToCatIso .Iso.rightInv _ = isProp-CatIso _ _
