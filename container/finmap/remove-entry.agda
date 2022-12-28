{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.remove-entry where

open import base
open import container.finmap
open import container.finmap.filter-map
open import equality
open import hlevel
open import order
open import order.instances.nat
open import relation

module _ {ℓK : Level} {ℓV : Level} {K : Type ℓK} {V : Type ℓV} {{disc'K : Discrete' K}} where
  private
    discK = Discrete'.f disc'K
