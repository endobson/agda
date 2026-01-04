{-# OPTIONS --cubical --safe --exact-split #-}

module semidomain where

open import additive-group
open import additive-group.apartness
open import apartness
open import base
open import equality-path
open import relation
open import semiring

module _
  {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#}
  {ACM : AdditiveCommMonoid D}
  (S : Semiring ACM)
  (A : isTightApartness D#) where
  private
    instance
      IACM = ACM
      IS = S
      IA = A

  record Semidomain : Type (ℓ-suc (ℓ-max ℓ ℓ#)) where
    field
      1#0 : 1# # 0#
      StronglyInjective-*₁ : (a : D) -> (a # 0#) -> StronglyInjective (a *_)
      StronglyExtensional-*₁ : (a : D) -> StronglyExtensional (a *_)

module _
  {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#}
  {{ACM : AdditiveCommMonoid D}}
  {{S : Semiring ACM}}
  {{A : isTightApartness D#}}
  {{SD : Semidomain S A}} where
  opaque
    *₁-preserves-# : {a b c : D} -> a # 0# -> b # c -> (a * b) # (a * c)
    *₁-preserves-# a#0 b#c =
      Semidomain.StronglyInjective-*₁ SD _ a#0 b#c

    *-preserves-#0 : {a b : D} -> a # 0# -> b # 0# -> (a * b) # 0#
    *-preserves-#0 {a} {b} a#0 b#0 =
      subst ((a * b) #_) *-right-zero (*₁-preserves-# a#0 b#0)

    *₁-reflects-# : {a b c : D} -> (a * b) # (a * c) -> b # c
    *₁-reflects-# =
      Semidomain.StronglyExtensional-*₁ SD _

    *₁-reflects-#0 : {a b : D} -> (a * b) # 0# -> b # 0#
    *₁-reflects-#0 {a} {b} ab#0 =
      *₁-reflects-# (subst ((a * b) #_) (sym *-right-zero) ab#0)

    *₂-reflects-#0 : {a b : D} -> (a * b) # 0# -> a # 0#
    *₂-reflects-#0 ab#0 =
      *₁-reflects-#0 (subst (_# 0#) *-commute ab#0)

    *₁-reflects-= : {a b c : D} -> a # 0# -> (a * b) == (a * c) -> b == c
    *₁-reflects-= {a} {b} {c} a#0 ab=ac = tight-# ¬b#c
      where
      ¬b#c : ¬ (b # c)
      ¬b#c b#c = irrefl-path-# ab=ac (*₁-preserves-# a#0 b#c)

    *₂-reflects-= : {a b c : D} -> c # 0# -> (a * c) == (b * c) -> a == b
    *₂-reflects-= c#0 ac=bc = *₁-reflects-= c#0 (*-commute >=> ac=bc >=> *-commute)
