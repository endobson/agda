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
open import truncation


module _ {ℓ : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         (R : Ring S AG) (A : TightApartnessStr D) where
  private
    module R = Ring R
    instance
      IS = S
      IACM = ACM
      IAG = AG
      IR = R
      IA = A

  record IntegralDomain : Type (ℓ-suc ℓ) where
    field
      1#0 : 1# # 0#
      diff-#-equiv : {a b : D} -> (a # b) ≃ (diff a b # 0#)
      *-#0-equiv : {a b : D} -> ((a # 0#) × (b # 0#)) ≃ (a * b) # 0#


module _ {ℓ : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {R : Ring S AG} {A : TightApartnessStr D} {{IntD : IntegralDomain R A}} where
  private
    module R = Ring R
    instance
      IACM = ACM
      IAG = AG
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

    +-#-equiv : {a b c : D} -> (b # c) ≃ ((a + b) # (a + c))
    +-#-equiv {a} {b} {c} =
      diff-#-equiv >eq>
      pathToEquiv (cong (_# 0#) p) >eq>
      (equiv⁻¹ diff-#-equiv)
      where
      p : (diff b c) == diff (a + b) (a + c)
      p = sym +-left-zero >=> +-left (sym +-inverse) >=> +-swap-diff

  abstract
    *₁-preserves-#0 : {a b : D} -> a # 0# -> b # 0# -> (a * b) # 0#
    *₁-preserves-#0 a#0 b#0 = eqFun *-#0-equiv (a#0 , b#0)

    *₁-reflects-#0 : {a b : D} -> (a * b) # 0# -> b # 0#
    *₁-reflects-#0 = snd ∘ eqInv *-#0-equiv

    *₂-reflects-#0 : {a b : D} -> (a * b) # 0# -> a # 0#
    *₂-reflects-#0 = fst ∘ eqInv *-#0-equiv

    *₁-preserves-# : {a b c : D} -> a # 0# -> b # c -> (a * b) # (a * c)
    *₁-preserves-# a#0 b#c = eqFun *-#-equiv (a#0 , b#c)

    *₁-reflects-# : {a b c : D} -> (a * b) # (a * c) -> b # c
    *₁-reflects-# = snd ∘ eqInv *-#-equiv

    *₁-reflects-= : {a b c : D} -> a # 0# -> (a * b) == (a * c) -> b == c
    *₁-reflects-= {a} {b} {c} a#0 ab=ac = tight-# ¬b#c
      where
      ¬b#c : ¬ (b # c)
      ¬b#c b#c = irrefl-path-# ab=ac (*₁-preserves-# a#0 b#c)

    *₂-reflects-= : {a b c : D} -> c # 0# -> (a * c) == (b * c) -> a == b
    *₂-reflects-= c#0 ac=bc = *₁-reflects-= c#0 (*-commute >=> ac=bc >=> *-commute)

    +₁-preserves-# : {a b c : D} -> b # c -> (a + b) # (a + c)
    +₁-preserves-# = eqFun +-#-equiv

    +₂-preserves-# : {a b c : D} -> a # b -> (a + c) # (b + c)
    +₂-preserves-# a#b = subst2 _#_ +-commute +-commute (+₁-preserves-# a#b)

    +₁-reflects-# : {a b c : D} -> (a + b) # (a + c) -> b # c
    +₁-reflects-# = eqInv +-#-equiv

    +-reflects-#0 : {a b : D} -> (a + b) # 0# -> ∥ (a # 0#) ⊎ (b # 0#) ∥
    +-reflects-#0 {a} {b} ab#0 = ∥-map handle (comparison-# _ a _ ab#0)
      where
      handle : ((a + b) # a) ⊎ (a # 0#) -> (a # 0#) ⊎ (b # 0#)
      handle (inj-r a#0)  = inj-l a#0
      handle (inj-l ab#a) = inj-r (+₁-reflects-# (subst2 _#_ refl (sym +-right-zero) ab#a))

    minus-reflects-# : {a b : D} -> a # b -> (- a) # (- b)
    minus-reflects-# a#b = subst2 _#_ R.*-left-minus-one R.*-left-minus-one
                                      (*₁-preserves-# -1#0 a#b)
      where
      -1#0 : (- 1#) # 0#
      -1#0 = subst2 _#_ +-left-zero +-inverse (+₂-preserves-# (sym-# 1#0))
