{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.int where

open import additive-group
open import additive-group.instances.int
open import abs
open import base
open import equality
open import int
open import int.order hiding (_≤_ ; _<_ ; trans-≤-< ; weaken-<)
open import nat
open import order
open import order.instances.int
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.instances.int
open import ring.implementations.int
open import semiring
open import semiring.initial
open import truncation

private
  abstract
    prop : ArchimedeanPropertyⁱ ℤ
    prop {a} {b} 0<a 0<b@((suc i , _) , p) = ∣ n , a<nb ∣
      where
      n : ℕ
      n = suc (abs' a)
      1≤b : 1# ≤ b
      1≤b = i , +-commute >=> +-eval >=> sym +-right-zero >=> p
      a<n : a < ℕ->ℤ n
      a<n = (1 , tt) , +-eval >=> cong add1 (nonneg-abs' a (≥0->NonNeg (weaken-< 0<a)))

      a<nb : a < (ℕ->Semiring n * b)
      a<nb = trans-≤-< (trans-=-≤ (sym *-right-one) (*₁-preserves-≤ (weaken-< 0<a) 1≤b))
                       (trans-<-= (*₂-preserves-< a<n 0<b) (*-left (sym (ℕ->Semiring-ℤ-path n))))

instance
  ArchimedeanSemring-ℤ : ArchimedeanSemiringⁱ ℤ
  ArchimedeanSemring-ℤ = record { prop = prop }
