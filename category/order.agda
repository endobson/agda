{-# OPTIONS --cubical --safe --exact-split #-}

module category.order where

open import base
open import category.base
open import equality-path
open import hlevel
open import isomorphism
open import order

private
  variable
    ℓObj ℓMor : Level

module _ (D : Type ℓObj) {{PO : PartialOrderStr D ℓMor}} where
  PartialOrderC : PreCategory ℓObj ℓMor
  PartialOrderC .PreCategory.Obj = D
  PartialOrderC .PreCategory.Mor x y = x ≤ y
  PartialOrderC .PreCategory.id = refl-≤
  PartialOrderC .PreCategory._⋆_ = trans-≤
  PartialOrderC .PreCategory.⋆-left-id f = isProp-≤ _ _
  PartialOrderC .PreCategory.⋆-right-id f = isProp-≤ _ _
  PartialOrderC .PreCategory.⋆-assoc f g h = isProp-≤ _ _
  PartialOrderC .PreCategory.isSet-Mor = isProp->isSet isProp-≤

  isThin-PartialOrderC : isThin PartialOrderC
  isThin-PartialOrderC .isThin.isProp-Mor = isProp-≤

  isUnivalent-PartialOrderC : isSet D -> isUnivalent PartialOrderC
  isUnivalent-PartialOrderC isSet-D .isUnivalent.isEquiv-pathToCatIso x y =
    isoToIsEquiv Iso-pathToCatIso
    where
    isProp-CatIso : isProp (CatIso PartialOrderC x y)
    isProp-CatIso c1 c2 = (\i -> record
      { mor = mor-path i
      ; inv = inv-path i
      ; sec = sec-path i
      ; ret = ret-path i
      })
      where
      mor-path : (CatIso.mor c1) == (CatIso.mor c2)
      mor-path i = isProp-≤ (CatIso.mor c1) (CatIso.mor c2) i
      inv-path : (CatIso.inv c1) == (CatIso.inv c2)
      inv-path i = isProp-≤ (CatIso.inv c1) (CatIso.inv c2) i
      sec-path : PathP (\i -> inv-path i ⋆⟨ PartialOrderC ⟩ mor-path i == refl-≤)
                       (CatIso.sec c1) (CatIso.sec c2)
      sec-path = isProp->PathP (\i -> isProp->isSet isProp-≤ _ _)
      ret-path : PathP (\i -> mor-path i ⋆⟨ PartialOrderC ⟩ inv-path i == refl-≤)
                       (CatIso.ret c1) (CatIso.ret c2)
      ret-path = isProp->PathP (\i -> isProp->isSet isProp-≤ _ _)


    Iso-pathToCatIso : Iso (x == y) (CatIso PartialOrderC x y)
    Iso-pathToCatIso .Iso.fun = pathToCatIso PartialOrderC x y
    Iso-pathToCatIso .Iso.inv c =
      antisym-≤ (CatIso.mor c) (CatIso.inv c)
    Iso-pathToCatIso .Iso.leftInv _ = isSet-D _ _ _ _
    Iso-pathToCatIso .Iso.rightInv _ = isProp-CatIso _ _
