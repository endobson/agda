{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain where

open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import functions
open import isomorphism
open import ring
open import semiring
open import sigma


module _ {ℓ : Level} {D : Type ℓ} {S : Semiring D}
         (R : Ring S) (A : TightApartnessStr D) where
  private
    module R = Ring R
    instance
      IS = S
      IR = R
      IA = A

  record IntegralDomain : Type (ℓ-suc ℓ) where
    field
      1#0 : 1# # 0#
      diff-#-equiv : {a b : D} -> (a # b) ≃ (diff a b # 0#)
      *-#0-equiv : {a b : D} -> ((a # 0#) × (b # 0#)) ≃ (a * b) # 0#


module _ {ℓ : Level} {D : Type ℓ} {S : Semiring D}
         {R : Ring S} {A : TightApartnessStr D} {{IntD : IntegralDomain R A}} where
  private
    instance
      IS = S
      IR = R
      IA = A

    open IntegralDomain IntD

  private
    *-#-equiv : {a b c : D} -> ((a # 0#) × (b # c)) ≃ ((a * b) # (a * c))
    *-#-equiv =
      ×-equiv (idEquiv _) diff-#-equiv >eq>
      *-#0-equiv >eq>
      pathToEquiv (cong (_# 0#) *-distrib-diff-left) >eq>
      (equiv⁻¹ diff-#-equiv)

  *₁-preserves-# : {a b c : D} -> a # 0# -> b # c -> (a * b) # (a * c)
  *₁-preserves-# a#0 b#c = eqFun *-#-equiv (a#0 , b#c)

  *₁-reflects-# : {a b c : D} -> (a * b) # (a * c) -> b # c
  *₁-reflects-# = snd ∘ eqInv *-#-equiv
