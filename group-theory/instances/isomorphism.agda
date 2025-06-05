{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.instances.isomorphism where

open import base
open import group
open import equality-path
open import hlevel.base
open import hlevel.pi
open import hlevel
open import hlevel.isomorphism
open import isomorphism
open import isomorphism.set

module _ {ℓ : Level} {A : Type ℓ} {{isSet'-A : isSet' A}} where
  private
    isSet-A : isSet A
    isSet-A = isSet'.f isSet'-A
    iso-path : {x y : Iso A A} -> Iso.fun x == Iso.fun y -> x == y
    iso-path = isSet-iso-path isSet-A isSet-A

  instance
    GroupStr-Iso : GroupStr (Iso A A)
    GroupStr-Iso = record
      { monoid = record
        { _∙_ = _>iso>_
        ; ε = id-iso
        ; ∙-assoc = iso-path refl
        ; ∙-left-ε = iso-path refl
        ; ∙-right-ε = iso-path refl
        ; isSet-Domain = isSet-Iso isSet-A isSet-A
        }
      ; inverse = iso⁻¹
      ; ∙-left-inverse = \{i} -> iso-path (\j a -> Iso.rightInv i a j)
      ; ∙-right-inverse = \{i} -> iso-path (\j a -> Iso.leftInv i a j)
      }
