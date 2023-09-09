{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import equality
open import hlevel

module category.constructions.lift where

module _ {ℓCo ℓCm : Level} (ℓDo ℓDm : Level) (C : PreCategory ℓCo ℓCm) where
  open CategoryHelpers C

  private
    LiftSorts : CategorySorts (ℓ-max ℓCo ℓDo) (ℓ-max ℓCm ℓDm)
    LiftSorts .CategorySorts.Obj = Lift ℓDo (Obj C)
    LiftSorts .CategorySorts.Mor (lift a) (lift b) = Lift ℓDm (C [ a , b ])

    LiftOps : CategoryOps LiftSorts
    LiftOps .CategoryOps.id = lift (id C)
    LiftOps .CategoryOps._⋆_ (lift f) (lift g) = lift (f ⋆ g)

    LiftLaws : CategoryLaws LiftOps
    LiftLaws .CategoryLaws.⋆-left-id _ = cong lift ⋆-left-id
    LiftLaws .CategoryLaws.⋆-right-id _ = cong lift ⋆-right-id
    LiftLaws .CategoryLaws.⋆-assoc _ _ _ = cong lift ⋆-assoc
    LiftLaws .CategoryLaws.isSet-Mor = isSet-Lift (isSet-Mor C)

  LiftC : PreCategory (ℓ-max ℓCo ℓDo) (ℓ-max ℓCm ℓDm)
  LiftC = Laws->Category LiftLaws
