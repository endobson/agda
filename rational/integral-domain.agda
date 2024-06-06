{-# OPTIONS --cubical --safe --exact-split #-}

module rational.integral-domain where

open import heyting-field.instances.rational
open import integral-domain
open import integral-domain.instances.heyting-field
open import rational

instance
  IntegralDomain-ℚ : IntegralDomain Ring-ℚ isTightApartness-ℚ#
  IntegralDomain-ℚ = IntegralDomain-Field
