{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.int where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int.addition
open import int.base
open import int.order
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
  ℕ-prop : (a : ℕ) (b : ℤ) (0<b : 0# < b) -> ∃[ n ∈ ℕ ] (int a < (ℕ->Semiring n * b))
  ℕ-prop a b 0<b = ∣ n , a<nb ∣
    where
    n : ℕ
    n = suc a
    1≤b : 1# ≤ b
    1≤b = add1-weaken-< 0<b
    a<n : int a < ℕ->ℤ n
    a<n = (1 , tt) , ℤ+-eval

    a<nb : int a < (ℕ->Semiring n * b)
    a<nb = trans-≤-< (trans-=-≤ (sym *-right-one) (*₁-preserves-≤ 0≤nonneg 1≤b))
                     (trans-<-= (*₂-preserves-< a<n 0<b) (*-left (sym (ℕ->Semiring-ℤ-path n))))


  opaque
    prop : ArchimedeanPropertyⁱ ℤ
    prop {a} {b} ((a' , _) , p) 0<b =
      transport (\i -> ∃[ n ∈ ℕ ] (p' i < (ℕ->Semiring n * b)))
        (ℕ-prop a' b 0<b)
      where
      p' : int a' == a
      p' = sym +-right-zero >=> p

instance
  ArchimedeanSemring-ℤ : ArchimedeanSemiringⁱ ℤ
  ArchimedeanSemring-ℤ = record { prop = prop }
