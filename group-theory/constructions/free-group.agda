{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.constructions.free-group where

open import base
open import equality-path
open import hlevel.base
open import hlevel.htype

module _ {ℓ : Level} ((D , isSet-D) : hSet ℓ) where
  data FreeCGroup : Type ℓ where
    base : FreeCGroup
    [_] : D -> base == base
    squash : isGroupoid FreeCGroup

  FreeGroup : Type ℓ
  FreeGroup = base == base
