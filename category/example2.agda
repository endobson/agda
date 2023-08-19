{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.example2 where

open import base
open import hlevel
open import equality
open import equality.inductive-data
open import category.base
open import category.constructions.iterated-product
open import category.constructions.functor-cat
open import category.displayed
open import category.monoidal.base
open import nat

module _ {ℓObj : Level} {D : Type ℓObj} (isGroupoid-D : isGroupoid D) where
  DiscreteC : PreCategory ℓObj ℓObj
  DiscreteC .PreCategory.Obj = D
  DiscreteC .PreCategory.Mor x y = x === y
  DiscreteC .PreCategory.id = refl-===
  DiscreteC .PreCategory._⋆_ = trans-===
  DiscreteC .PreCategory.⋆-left-id refl-=== = refl
  DiscreteC .PreCategory.⋆-right-id refl-=== = refl
  DiscreteC .PreCategory.⋆-assoc refl-=== refl-=== refl-=== = refl
  DiscreteC .PreCategory.isSet-Mor = ≃-isSet Path≃Eq (isGroupoid-D _ _)

module _ {ℓI ℓO ℓM : Level} {Idx : Type ℓI}
         (isGroupoid-I : isGroupoid Idx)
         (C : (i : Idx) -> PreCategory ℓO ℓM) where

  UnionCᴰ : PreCategoryᴰ (DiscreteC isGroupoid-I) ℓO ℓM
  UnionCᴰ .PreCategoryᴰ.Objᴰ i = Obj (C i)
  UnionCᴰ .PreCategoryᴰ.Morᴰ {i} refl-=== f1 f2 = (C i) [ f1 , f2 ]
  UnionCᴰ .PreCategoryᴰ.idᴰ {i} = id (C i)
  UnionCᴰ .PreCategoryᴰ._⋆ᴰ_ {i} {_} {_} {refl-===} {refl-===} f1 f2 =
    f1 ⋆⟨ C i ⟩ f2
  UnionCᴰ .PreCategoryᴰ.⋆ᴰ-left-id {i} {_} {refl-===} f =
    PreCategory.⋆-left-id (C i) f
  UnionCᴰ .PreCategoryᴰ.⋆ᴰ-right-id {i} {_} {refl-===} f =
    PreCategory.⋆-right-id (C i) f
  UnionCᴰ .PreCategoryᴰ.⋆ᴰ-assoc {i} {_} {_} {_} {refl-===} {refl-===} {refl-===} f g h =
    PreCategory.⋆-assoc (C i) f g h
  UnionCᴰ .PreCategoryᴰ.isSet-Morᴰ {i} {_} {refl-===} = PreCategory.isSet-Mor (C i)

  UnionC : PreCategory (ℓ-max ℓI ℓO) (ℓ-max ℓI ℓM)
  UnionC = TotalC UnionCᴰ
