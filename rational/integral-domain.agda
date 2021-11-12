{-# OPTIONS --cubical --safe --exact-split #-}

module rational.integral-domain where

open import integral-domain
open import integral-domain.instances.heyting-field
open import rational
open import rational.heyting-field

instance
  IntegralDomain-ℚ : IntegralDomain RationalRing TightApartnessStr-ℚ
  IntegralDomain-ℚ = IntegralDomain-Field