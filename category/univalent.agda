{-# OPTIONS --cubical --safe --exact-split #-}

module category.univalent where

open import base
open import category.base
open import category.isomorphism
open import equality-path
open import equality.identity-system
open import equivalence
open import funext
open import isomorphism
open import sigma.base

private
  variable
    ℓO ℓM : Level

record CatIso (C : PreCategory ℓO ℓM) (x y : C .Obj) : Type (ℓ-max ℓO ℓM) where
  constructor cat-iso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

idCatIso : (C : PreCategory ℓO ℓM) (x : C .Obj) -> CatIso C x x
idCatIso C x = record
  { mor = C .id
  ; inv = C .id
  ; sec = PreCategory.⋆-left-id C _
  ; ret = PreCategory.⋆-left-id C _
  }

module _ {C : PreCategory ℓO ℓM} {x y : C .Obj} where
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

pathToCatIso : (C : PreCategory ℓO ℓM) (x y : C .Obj) -> x == y -> CatIso C x y
pathToCatIso C x _ = J (\ y _ -> CatIso C x y) (idCatIso C x)

pathToCatIso-refl : (C : PreCategory ℓO ℓM) (x : C .Obj) ->
                    pathToCatIso C x x refl == idCatIso C x
pathToCatIso-refl C x = JRefl (\ y _ -> CatIso C x y) (idCatIso C x)

record isUnivalent (C : PreCategory ℓO ℓM) : Type (ℓ-max ℓO ℓM) where
  field
    isEquiv-pathToCatIso : (x y : C .Obj) -> isEquiv (pathToCatIso C x y)

isUnivalent' : {ℓO ℓM : Level} -> PreCategory ℓO ℓM -> Type (ℓ-max ℓO ℓM)
isUnivalent' C = isIdentitySystem (CatIso C) (idCatIso C)

isUnivalent->isUnivalent' : {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} ->
  isUnivalent C -> isUnivalent' C
isUnivalent->isUnivalent' {C = C} univ =
  transport (\i -> isIdentitySystem (CatIso C) (\a -> pathToCatIso-refl C a i)) ids
  where
  ids : isIdentitySystem (CatIso C) (\a -> pathToCatIso C a a refl)
  ids = isIdentitySystem-Equiv (_ , isUnivalent.isEquiv-pathToCatIso univ _ _)

isUnivalent'->isUnivalent : {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} ->
  isUnivalent' C -> isUnivalent C
isUnivalent'->isUnivalent {C = C} univ .isUnivalent.isEquiv-pathToCatIso x y =
  rightInverse-isEquiv to-path (pathToCatIso C x y) (funExt p')
    (isIdentitySystem->isEquiv univ)
  where
  open isIdentitySystem univ
  p' : ∀ {x y} (p : x == y) -> to-path (pathToCatIso C x y p) == p
  p' {x} {y} = J (\y p -> to-path (pathToCatIso C x y p) == p)
                 (cong to-path (pathToCatIso-refl C x) >=>
                  Ids-refl univ x)
