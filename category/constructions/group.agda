{-# OPTIONS --cubical --safe --exact-split #-}

-- The internal group objects of a category

module category.constructions.group where

open import base
open import category.base
open import category.functor
open import equality-path
open import category.monoidal.base
open import category.monoidal.cartesian
open import category.object.group

module _ {ℓO ℓM : Level} (CMC@((C , M) , Cart) : CartesianMonoidalCategory ℓO ℓM)  where
  open MonoidalStrHelpers M
  open CategoryHelpers C
  open CartesianHelpers Cart

  IGroupC : PreCategory (ℓ-max ℓO ℓM) ℓM
  IGroupC = Laws->Category GroupLaws
    where
    GroupSorts : CategorySorts (ℓ-max ℓO ℓM) ℓM
    GroupSorts .CategorySorts.Obj = GroupObject CMC
    GroupSorts .CategorySorts.Mor = GroupHomomorphism

    GroupOps : CategoryOps GroupSorts
    GroupOps .CategoryOps.id = record
      { mor = id C
      ; commutes = ⋆-right-id >=> sym (⋆-left (F-id ⊗ _) >=> ⋆-left-id)
      }
    GroupOps .CategoryOps._⋆_
      (record { mor = mor1 ; commutes = commutes1 })
      (record { mor = mor2 ; commutes = commutes2 }) = record
      { mor = mor1 ⋆ mor2
      ; commutes =
        sym ⋆-assoc >=>
        ⋆-left commutes1 >=>
        ⋆-assoc >=>
        ⋆-right commutes2 >=>
        sym ⋆-assoc >=>
        ⋆-left (sym ⊗-distrib-⋆)
      }

    GroupLaws : CategoryLaws GroupOps
    GroupLaws .CategoryLaws.⋆-left-id _ =
      group-homomorphism-path ⋆-left-id
    GroupLaws .CategoryLaws.⋆-right-id _ =
      group-homomorphism-path ⋆-right-id
    GroupLaws .CategoryLaws.⋆-assoc _ _ _ =
      group-homomorphism-path ⋆-assoc
    GroupLaws .CategoryLaws.isSet-Mor = isSet-GroupHomomorphism
