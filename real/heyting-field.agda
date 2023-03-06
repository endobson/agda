{-# OPTIONS --cubical --safe --exact-split #-}

module real.heyting-field where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import heyting-field
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import real
open import real.apartness
open import ring.implementations.real
open import sum
open import truncation
open import univalence


private
  +₁-reflects-ℝ< : {a b c : ℝ} -> (a + b) < (a + c) -> b < c
  +₁-reflects-ℝ< {a} ab<ac = subst2 _<_ p p (+₁-preserves-< ab<ac)
    where
    p : {x : ℝ} -> (- a + (a + x)) == x
    p = sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero

  +₂-reflects-ℝ< : {a b c : ℝ} -> (a + c) < (b + c) -> a < b
  +₂-reflects-ℝ< ac<bc = +₁-reflects-ℝ< (subst2 _<_ +-commute +-commute ac<bc)

  +-reflects-ℝ< : {a b c d : ℝ} -> (a + b) < (c + d) -> ∥ (a < c) ⊎ (b < d) ∥
  +-reflects-ℝ< {a} {b} {c} {d} ab<cd = ∥-map handle (comparison-< _ (c + b) _ ab<cd)
    where
    handle : ((a + b) < (c + b)) ⊎ ((c + b) < (c + d)) -> (a < c) ⊎ (b < d)
    handle = ⊎-map +₂-reflects-ℝ< +₁-reflects-ℝ<

instance
  ℝField : Field ℝRing TightApartnessStr-ℝ
  ℝField = record
    { f#-path = (sym (funExt2 (\x y -> (ua (ℝ#≃diff# x y)))))
    }

  abstract
    ApartAdditiveGroup-ℝ : ApartAdditiveGroup AdditiveGroup-ℝ TightApartnessStr-ℝ
    ApartAdditiveGroup-ℝ = record
      { +-reflects-# = +-reflects-ℝ#
      }
      where
      +-reflects-ℝ# : {a b c d : ℝ} -> (a + b) # (c + d) -> ∥ (a # c) ⊎ (b # d) ∥
      +-reflects-ℝ# (inj-l ab<cd) = ∥-map (⊎-map inj-l inj-l) (+-reflects-ℝ< ab<cd)
      +-reflects-ℝ# (inj-r ab>cd) = ∥-map (⊎-map inj-r inj-r) (+-reflects-ℝ< ab>cd)
