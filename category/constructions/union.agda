{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.constructions.union where

open import base
open import hlevel
open import equality
open import category.base
open import category.instances.discrete
open import category.displayed

module _ {ℓI ℓO ℓM : Level} {Idx : Type ℓI}
         (isGroupoid-Idx : isGroupoid Idx)
         (C : (i : Idx) -> PreCategory ℓO ℓM) where
  open PreCategoryᴰ

  UnionCᴰ : PreCategoryᴰ (DiscreteC' isGroupoid-Idx) ℓO ℓM
  UnionCᴰ .Objᴰ i = Obj (C i)
  UnionCᴰ .Morᴰ {i} refl-=== f1 f2 = (C i) [ f1 , f2 ]
  UnionCᴰ .idᴰ {i} = id (C i)
  UnionCᴰ ._⋆ᴰ_ {i} {_} {_} {refl-===} {refl-===} f1 f2 =
    f1 ⋆⟨ C i ⟩ f2
  UnionCᴰ .⋆ᴰ-left-id {i} {_} {refl-===} f =
    PreCategory.⋆-left-id (C i) f
  UnionCᴰ .⋆ᴰ-right-id {i} {_} {refl-===} f =
    PreCategory.⋆-right-id (C i) f
  UnionCᴰ .⋆ᴰ-assoc {i} {_} {_} {_} {refl-===} {refl-===} {refl-===} f g h =
    PreCategory.⋆-assoc (C i) f g h
  UnionCᴰ .isSet-Morᴰ {i} {_} {refl-===} = PreCategory.isSet-Mor (C i)

  UnionC : PreCategory (ℓ-max ℓI ℓO) (ℓ-max ℓI ℓM)
  UnionC = TotalC UnionCᴰ
