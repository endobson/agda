{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.nat where

open import additive-group.instances.nat
open import base
open import equality
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.instances.nat
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import truncation

private
  opaque
    prop : ArchimedeanPropertyⁱ ℕ
    prop {a} {b} 0<a 0<b = ∣ (suc a) , a<sab ∣
      where
      a<sa : a < suc a
      a<sa = refl-≤

      a<sab : a < (suc a * b)
      a<sab =
        (trans-≤-< (trans-=-≤ (sym *-right-one) (*₁-preserves-≤ (weaken-< 0<a) 0<b))
                   (*₂-preserves-< a<sa 0<b))

instance
  ArchimedeanSemring-ℕ : ArchimedeanSemiringⁱ ℕ
  ArchimedeanSemring-ℕ = record { prop = prop }
