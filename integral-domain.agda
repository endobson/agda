{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain where

open import additive-group
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


module _ {ℓ ℓ# : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         (R : Ring S AG) (A : TightApartnessStr D ℓ#) where
  private
    instance
      IS = S
      IACM = ACM
      IAG = AG
      IR = R
      IA = A

  record IntegralDomain : Type (ℓ-suc (ℓ-max ℓ ℓ#)) where
    field
      1#0 : 1# # 0#
      diff-#-equiv : {a b : D} -> (a # b) ≃ (diff a b # 0#)
      *-#0-equiv : {a b : D} -> ((a # 0#) × (b # 0#)) ≃ (a * b) # 0#


module _ {ℓ ℓ# : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {R : Ring S AG} {A : TightApartnessStr D ℓ#} {{IntD : IntegralDomain R A}} where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
      IR = R
      IA = A

    open IntegralDomain IntD hiding (diff-#-equiv)

  abstract
    diff-#-equiv : {a b : D} -> (a # b) ≃ (diff a b # 0#)
    diff-#-equiv = IntegralDomain.diff-#-equiv IntD

  private
    *-#-equiv : {a b c : D} -> ((a # 0#) × (b # c)) ≃ ((a * b) # (a * c))
    *-#-equiv =
      ×-equiv (idEquiv _) diff-#-equiv >eq>
      *-#0-equiv >eq>
      pathToEquiv (cong (_# 0#) *-distrib-diff-left) >eq>
      (equiv⁻¹ diff-#-equiv)

    +-#-equiv : {a b c : D} -> (b # c) ≃ ((a + b) # (a + c))
    +-#-equiv {a} {b} {c} =
      diff-#-equiv >eq>
      pathToEquiv (cong (_# 0#) p) >eq>
      (equiv⁻¹ diff-#-equiv)
      where
      p : (diff b c) == diff (a + b) (a + c)
      p = sym +-left-zero >=> +-left (sym +-inverse) >=> +-swap-diff

  abstract
    *-preserves-#0 : {a b : D} -> a # 0# -> b # 0# -> (a * b) # 0#
    *-preserves-#0 a#0 b#0 = eqFun *-#0-equiv (a#0 , b#0)

    *₁-reflects-#0 : {a b : D} -> (a * b) # 0# -> b # 0#
    *₁-reflects-#0 = snd ∘ eqInv *-#0-equiv

    *₂-reflects-#0 : {a b : D} -> (a * b) # 0# -> a # 0#
    *₂-reflects-#0 = fst ∘ eqInv *-#0-equiv

    *₁-preserves-# : {a b c : D} -> a # 0# -> b # c -> (a * b) # (a * c)
    *₁-preserves-# a#0 b#c = eqFun *-#-equiv (a#0 , b#c)

    *₁-reflects-# : {a b c : D} -> (a * b) # (a * c) -> b # c
    *₁-reflects-# = snd ∘ eqInv *-#-equiv

    *₁-fully-reflects-# : {a b c : D} -> (a * b) # (a * c) -> (a # 0#) × (b # c)
    *₁-fully-reflects-# = eqInv *-#-equiv

    *₁-reflects-= : {a b c : D} -> a # 0# -> (a * b) == (a * c) -> b == c
    *₁-reflects-= {a} {b} {c} a#0 ab=ac = tight-# ¬b#c
      where
      ¬b#c : ¬ (b # c)
      ¬b#c b#c = irrefl-path-# ab=ac (*₁-preserves-# a#0 b#c)

    *₂-reflects-= : {a b c : D} -> c # 0# -> (a * c) == (b * c) -> a == b
    *₂-reflects-= c#0 ac=bc = *₁-reflects-= c#0 (*-commute >=> ac=bc >=> *-commute)

    +₁-reflects-# : {a b c : D} -> (a + b) # (a + c) -> b # c
    +₁-reflects-# = eqInv +-#-equiv
