{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.discrete where

open import base
open import category.base
open import category.univalent
open import cubical
open import equality-path
open import equality.identity-system
open import equality.inductive-data
open import hlevel

private
  variable
    ℓObj ℓMor : Level

module _ {D : Type ℓObj} (isGroupoid-D : isGroupoid D) where
  DiscreteC : PreCategory ℓObj ℓObj
  DiscreteC .PreCategory.Obj = D
  DiscreteC .PreCategory.Mor x y = x == y
  DiscreteC .PreCategory.id = refl
  DiscreteC .PreCategory._⋆_ = _>=>_
  DiscreteC .PreCategory.⋆-left-id = compPath-refl-left
  DiscreteC .PreCategory.⋆-right-id = compPath-refl-right
  DiscreteC .PreCategory.⋆-assoc = compPath-assoc
  DiscreteC .PreCategory.isSet-Mor = isGroupoid-D _ _

  module _ where
    open isIdentitySystem
    isUnivalent'-DiscreteC : isUnivalent' DiscreteC
    isUnivalent'-DiscreteC .to-path (cat-iso p _ _ _) = p
    isUnivalent'-DiscreteC .to-path-over {a} {b} (cat-iso p _ _ _) =
      transP-left
        (transport-filler (\i -> CatIso DiscreteC a (p i)) (idCatIso DiscreteC a))
        (cat-iso-path (\j -> transp (\i -> a == (p (i ∨ j))) j (\i -> p (i ∧ j))))

module _ {D : Type ℓObj} (isGroupoid-D : isGroupoid D) where
  DiscreteC' : PreCategory ℓObj ℓObj
  DiscreteC' .PreCategory.Obj = D
  DiscreteC' .PreCategory.Mor x y = x === y
  DiscreteC' .PreCategory.id = refl-===
  DiscreteC' .PreCategory._⋆_ = trans-===
  DiscreteC' .PreCategory.⋆-left-id refl-=== = refl
  DiscreteC' .PreCategory.⋆-right-id refl-=== = refl
  DiscreteC' .PreCategory.⋆-assoc refl-=== refl-=== refl-=== = refl
  DiscreteC' .PreCategory.isSet-Mor {s} {t} = ≃-isSet Path≃Eq (isGroupoid-D _ _)
