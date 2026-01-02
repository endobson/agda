{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real where

open import additive-group
open import additive-group.instances.real
open import base
open import equality-path
open import equivalence
open import order
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.negated
open import ordered-semiring.ring
open import real
open import real.apartness
open import real.arithmetic.order
open import real.rational
open import ring
open import ring.implementations.real
open import semiring
open import semiring.unit
open import sum

instance
  LinearlyOrderedSemiringStr-ℝ : LinearlyOrderedSemiringStr ℝSemiring useⁱ
  LinearlyOrderedSemiringStr-ℝ = LinearlyOrderedSemiringStr-Ring
    (ℝ*₁-preserves-< _ _ _)

  PartiallyOrderedSemiringStr-ℝ : PartiallyOrderedSemiringStr ℝSemiring useⁱ
  PartiallyOrderedSemiringStr-ℝ = PartiallyOrderedSemiringStr-Negated _ _

  NonTrivalLinearlyOrderedSemiringStr-ℝ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℝ
  NonTrivalLinearlyOrderedSemiringStr-ℝ = record { 0<1 = ℚ->ℝ-preserves-< 0<1 }

opaque
  instance
    StronglyLinearlyOrderedSemiringStr-ℝ : StronglyLinearlyOrderedSemiringStr ℝSemiring useⁱ
    StronglyLinearlyOrderedSemiringStr-ℝ = record
      { *₁-fully-reflects-< = *₁-fully-reflects-ℝ<
      }
      where
      module ℝ = Ring ℝRing

      *₁-fully-reflects-ℝ< : {a b c : ℝ} -> (a * b) < (a * c) ->
                             (b < c × 0# < a) ⊎ (c < b × a < 0#)
      *₁-fully-reflects-ℝ< {a} {b} {c} ab<ac = handle a<>0 b<>c
        where
        uabac : isUnit (diff (a * b) (a * c))
        uabac = eqFun (ℝ#≃diff# _ _) (inj-l ab<ac)
        ua-ubc : isUnit a × isUnit (diff b c)
        ua-ubc = *-isUnit-split (subst isUnit (sym *-distrib-diff-left) uabac)

        a<>0 : a <> 0#
        a<>0 = ⊎-swap (eqInv (ℝ#≃diff# 0# a) (subst isUnit (sym diff-step >=> +-left-zero) (proj₁ ua-ubc)))

        b<>c : b <> c
        b<>c = eqInv (ℝ#≃diff# b c) (proj₂ ua-ubc)

        handle : a <> 0# -> b <> c -> (b < c × 0# < a) ⊎ (c < b × a < 0#)
        handle (inj-l a<0) (inj-l b<c) =
          bot-elim (asym-< ab<ac (*₁-flips-< a<0 b<c))
        handle (inj-l a<0) (inj-r c<b) = inj-r (c<b , a<0)
        handle (inj-r 0<a) (inj-l b<c) = inj-l (b<c , 0<a)
        handle (inj-r 0<a) (inj-r c<b) =
          bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))
