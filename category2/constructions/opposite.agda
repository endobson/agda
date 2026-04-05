{-# OPTIONS --cubical --safe --exact-split #-}

module category2.constructions.opposite where

open import base
open import equality-path
open import hlevel.base
open import category2.base

module _ {ℓO ℓM : Level} {O : Type ℓO} {M : Rel O ℓM}
  {{CS : CategoryStr M}}
  where

  record OpC→ (o₁ o₂ : O) : Type ℓM where
    constructor [_]
    field
      m : M o₂ o₁

  private
    isSet-OpC→ : ∀ {o₁ o₂} -> isSet (OpC→ o₁ o₂)
    isSet-OpC→ [ m₁ ] [ m₂ ] p₁ p₂ i j =
      [ isSet-Mor m₁ m₂ (cong OpC→.m p₁) (cong OpC→.m p₂) i j ]


  module _ where
    OpC-CategoryStr : CategoryStr OpC→
    OpC-CategoryStr = record
      { id = [ id ]
      ; _⋆_ = \{ [ m₁ ] [ m₂ ] -> [ m₂ ⋆ m₁ ] }
      ; ⋆-left-idᵉ = \_ -> cong [_] ⋆-right-id
      ; ⋆-right-idᵉ = \_ -> cong [_] ⋆-left-id
      ; ⋆-assocᵉ = \_ _ _ -> cong [_] (sym ⋆-assoc)
      ; isSet-Mor = isSet-OpC→
      }


module _ {ℓO ℓM : Level} (C@(category _ M CS) : Category ℓO ℓM) where

   OpC : Category ℓO ℓM
   OpC = Category▪ (OpC-CategoryStr {{CS = CS}})
