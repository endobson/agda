{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.remove where

open import base
open import container.finmap
open import container.finmap.partition-keys
open import discrete
open import equality
open import hlevel
open import order
open import order.instances.nat
open import relation

module _ {ℓK : Level} {ℓV : Level} {K : Type ℓK} {V : Type ℓV} {{disc'K : Discrete' K}} where
  finmap'-remove : K -> FinMap' K V -> FinMap' K V
  finmap'-remove k = finmap'-drop-keys (decide-= k)

  ¬HasKey-finmap'-remove : {m : FinMap' K V} -> (k : K) -> ¬ (HasKey' k (finmap'-remove k m))
  ¬HasKey-finmap'-remove {m = m} k = ¬HasKey-finmap'-drop-keys (decide-= k) {m} refl

  HasKey-finmap'-remove : {k2 : K} {m : FinMap' K V} -> (k : K) -> k != k2 -> HasKey' k2 m ->
                          (HasKey' k2 (finmap'-remove k m))
  HasKey-finmap'-remove k k!=k2 hk = HasKey-finmap'-drop-keys (decide-= k) k!=k2 hk

  fm⊆-finmap'-remove : (k : K) (m : FinMap' K V) -> finmap'-remove k m fm⊆ m
  fm⊆-finmap'-remove k m = fm⊆-finmap'-drop-keys (decide-= k) m

  fm'-size-finmap'-remove : (k : K) (m : FinMap' K V) -> fm'-size (finmap'-remove k m) ≤ fm'-size m
  fm'-size-finmap'-remove k m = fm'-size-finmap'-drop-keys (decide-= k) m
