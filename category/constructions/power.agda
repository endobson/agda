{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import fin-algebra
open import hlevel.pi

module category.constructions.power where

module _ {ℓCo ℓCm : Level} (C : PreCategory ℓCo ℓCm) where
  private
    module C = PreCategory C

  ExpCat : {ℓI : Level} -> Type ℓI -> PreCategory (ℓ-max ℓI ℓCo) (ℓ-max ℓI ℓCm)
  ExpCat I = record
    { Obj = I -> Obj C
    ; Mor = \s t -> (i : I) -> C [ s i , t i ]
    ; id = \_ -> id C
    ; _⋆_ = \f g i -> f i ⋆⟨ C ⟩ g i
    ; ⋆-left-id = \f ii i -> C.⋆-left-id (f i) ii
    ; ⋆-right-id = \f ii i -> C.⋆-right-id (f i) ii
    ; ⋆-assoc = \f g h ii i -> C.⋆-assoc (f i) (g i) (h i) ii
    ; isSet-Mor = isSetΠ (\i -> isSet-Mor C)
    }

  PowerCat : (n : Nat) -> PreCategory ℓCo ℓCm
  PowerCat n = ExpCat (FinT n)
