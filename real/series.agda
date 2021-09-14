{-# OPTIONS --cubical --safe --exact-split #-}

module real.series where

open import base
open import real
open import real.sequence
open import finsum
open import fin
open import finset.instances
open import ring.implementations.rational

private
  Seq = ℚSequence

partial-sums : Seq -> Seq
partial-sums s n = finiteSum (\ ((i , _) : Fin n) -> s i)
