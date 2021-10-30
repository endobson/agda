{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.instances.real where

open import additive-group.instances.real
open import real.heyting-field
open import integral-domain
open import integral-domain.instances.heyting-field
open import ring.implementations.real

instance
  IntegralDomain-ℝ : IntegralDomain ℝRing TightApartnessStr-ℝ
  IntegralDomain-ℝ = IntegralDomain-Field
