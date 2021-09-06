{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.instances.heyting-field where

open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import heyting-field
open import hlevel
open import isomorphism
open import integral-domain
open import functions
open import funext
open import relation
open import ring
open import semiring
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {S : Semiring D} {R : Ring S} {A : TightApartnessStr D} {{F : Field R A}}
  where
  private
    module R = Ring R
    module F = Field F
    instance
      IS = S
      IR = R
      IA = A

    open F using (_f#_)


    diff-#-forward : {a b : D} -> a # b -> (diff a b) # 0#
    diff-#-forward {a} {b} a#b =
      subst2 _#_ refl +-inverse b-a#a-a
      where
      b-a#a-a : (b + (- a)) # (a + (- a))
      b-a#a-a = F.StronglyInjective-+₂ (sym-# a#b)

    diff-#-backward : {a b : D} -> (diff a b) # 0# -> a # b
    diff-#-backward {a} {b} b-a#0 =
      sym-# (subst2 _#_ (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                        +-left-zero b-aa#0a)
      where
      b-aa#0a : ((b + (- a)) + a) # (0# + a)
      b-aa#0a = F.StronglyInjective-+₂ b-a#0

    diff-#-equiv : {a b : D} -> (a # b) ≃ (diff a b # 0#)
    diff-#-equiv = isoToEquiv (isProp->iso diff-#-forward diff-#-backward isProp-# isProp-#)

    *-#0-forward : {a b : D} -> ((a # 0#) × (b # 0#)) -> (a * b) # 0#
    *-#0-forward (a#0 , b#0) =
      subst2 _#_ refl *-right-zero (F.StronglyInjective-*₁ a#0 b#0)

    *-#0-backward : {a b : D} -> (a * b) # 0# -> ((a # 0#) × (b # 0#))
    *-#0-backward = F.*-apart-zero

    *-#0-equiv : {a b : D} -> ((a # 0#) × (b # 0#)) ≃ ((a * b) # 0#)
    *-#0-equiv = isoToEquiv (isProp->iso *-#0-forward *-#0-backward
                                         (isProp× isProp-# isProp-#) isProp-#)


  abstract
    IntegralDomain-Field : IntegralDomain R A
    IntegralDomain-Field = record
      { 1#0 = F.1#0
      ; diff-#-equiv = diff-#-equiv
      ; *-#0-equiv = *-#0-equiv
      }
