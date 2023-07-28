{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import equality-path

module category.constructions.opposite where

module _ {ℓo ℓm : Level} (C : PreCategory ℓo ℓm) where
  private
    module C = PreCategory C

  OpCat : PreCategory ℓo ℓm
  OpCat = record
    { Obj = C.Obj
    ; Mor = OpMor
    ; id = C.id
    ; _⋆_ = \ f g -> g ⋆⟨ C ⟩ f
    ; ⋆-left-id = \f -> C.⋆-right-id f
    ; ⋆-right-id = \f -> C.⋆-left-id f
    ; ⋆-assoc = \ f g h -> sym (C.⋆-assoc h g f)
    ; isSet-Mor = C.isSet-Mor
    }
    where
    OpMor : (s t : C.Obj) -> Type ℓm
    OpMor s t = C [ t , s ]

module _ {ℓCo ℓCm ℓDo ℓDm : Level} {C : PreCategory ℓCo ℓCm} {D : PreCategory ℓDo ℓDm}
         (F : Functor C D) where
  private
    module F = Functor F

  op-functor : Functor (OpCat C) (OpCat D)
  op-functor .F-obj o = F.obj o
  op-functor .F-mor f = F.mor f
  op-functor .F-id o = F.id o
  op-functor .F-⋆ f g = F.⋆ g f


private
  Op-twice : {ℓo ℓm : Level} (c : PreCategory ℓo ℓm) -> OpCat (OpCat c) == c
  Op-twice _ = refl
