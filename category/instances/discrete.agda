{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.discrete where

open import base
open import category.base
open import category.univalent
open import cubical
open import equality-path
open import equality.identity-system
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


  module _ where
    open isIdentitySystem
    isUnivalent'-DiscreteC : isUnivalent' DiscreteC
    isUnivalent'-DiscreteC .to-path (cat-iso p _ _ _) = p
    isUnivalent'-DiscreteC .to-path-over {a} {b} (cat-iso p _ _ _) =
      transP-left
        (transport-filler (\i -> CatIso DiscreteC a (p i)) (idCatIso DiscreteC a))
        (cat-iso-path (\j -> transp (\i -> a == (p (i ∨ j))) j (\i -> p (i ∧ j))))
