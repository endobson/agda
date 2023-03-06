{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real-strong where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import order
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.apartness
open import ring
open import ring.implementations.real
open import semiring
open import sum

instance
  StronglyLinearlyOrderedSemiringStr-ℝ : StronglyLinearlyOrderedSemiringStr ℝSemiring LinearOrderStr-ℝ
  StronglyLinearlyOrderedSemiringStr-ℝ = record
    { *₁-fully-reflects-< = *₁-fully-reflects-ℝ<
    }
    where
    module ℝ = Ring ℝRing

    *₁-fully-reflects-ℝ< : {a b c : ℝ} -> (a * b) < (a * c) ->
                           (b < c × 0# < a) ⊎ (c < b × a < 0#)
    *₁-fully-reflects-ℝ< {a} {b} {c} ab<ac = handle a<>0 b<>c
      where
      uabac : ℝ.isUnit (diff (a * b) (a * c))
      uabac = eqFun (ℝ#≃diff# _ _) (inj-l ab<ac)
      ua-ubc : ℝ.isUnit a × ℝ.isUnit (diff b c)
      ua-ubc = ℝ.*-isUnit-split (subst ℝ.isUnit (sym *-distrib-diff-left) uabac)

      a<>0 : a <> 0#
      a<>0 = ⊎-swap (eqInv (ℝ#≃diff# 0# a) (subst ℝ.isUnit (sym diff-step >=> +-left-zero) (proj₁ ua-ubc)))

      b<>c : b <> c
      b<>c = eqInv (ℝ#≃diff# b c) (proj₂ ua-ubc)

      handle : a <> 0# -> b <> c -> (b < c × 0# < a) ⊎ (c < b × a < 0#)
      handle (inj-l a<0) (inj-l b<c) =
        bot-elim (asym-< ab<ac (*₁-flips-< a<0 b<c))
      handle (inj-l a<0) (inj-r c<b) = inj-r (c<b , a<0)
      handle (inj-r 0<a) (inj-l b<c) = inj-l (b<c , 0<a)
      handle (inj-r 0<a) (inj-r c<b) =
        bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))
