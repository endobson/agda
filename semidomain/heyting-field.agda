{-# OPTIONS --cubical --safe --exact-split #-}

module semidomain.heyting-field where

open import additive-group
open import apartness
open import base
open import heyting-field
open import relation
open import ring
open import semidomain
open import semiring

module _ {ℓ : Level} {D : Type ℓ} {D# : Rel D ℓ}
         {ACM : AdditiveCommMonoid D} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG} {A : isTightApartness D#}
         {{F : Field R A}}
  where
  private
    module F = Field F

  Semidomain-Field : Semidomain S A
  Semidomain-Field = record
    { 1#0 = F.1#0
    ; StronglyInjective-*₁ = \_ -> F.StronglyInjective-*₁
    ; StronglyExtensional-*₁ = \_ ab#ac -> proj₂ (F.*₁-apart-args ab#ac)
    }
