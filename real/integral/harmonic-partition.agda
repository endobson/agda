{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.harmonic-partition where

open import base
open import nat
open import nat.order
open import equality
open import order
open import order.instances.real
open import order.instances.nat
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import fin
open import real.rational
open import real.arithmetic.rational
open import additive-group
open import additive-group.instances.real
open import additive-group.instances.int
open import semiring
open import ring
open import ring.implementations.real
open import rational
open import rational.order
open import real.integral.partition

import int

harmonic-partition : {a b : ℝ} -> a < b -> Nat⁺ -> Partition a b
harmonic-partition {a} {b} a<b n⁺@(n , _) =
  record
  { n = n
  ; u = u
  ; u0=a = u0=a
  ; un=b = un=b
  ; u<u = u<u
  }
  where
  u : Fin (suc n) -> ℝ
  u (i , _) = (ℚ->ℝ (ℕ->ℚ i)) * (ℚ->ℝ (1/ℕ n⁺)) * (diff a b) + a

  u0=a : u zero-fin == a
  u0=a =
    +-left (*-left *-left-zero >=> *-left-zero) >=> +-left-zero

  un=b : u (n , same-≤ _) == b
  un=b =
    +-left (*-left (sym ℚ->ℝ-preserves-* >=>
                    cong ℚ->ℝ (*-commute >=> (1/ℕ-ℕ-path n⁺))) >=>
            *-left-one) >=>
    +-commute >=>
    diff-step

  0<diff : 0# < diff a b
  0<diff = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)

  u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)
  u<u (i , _) =
    +₂-preserves-< (*₂-preserves-<
      (*₂-preserves-<
        (ℚ->ℝ-preserves-< _ _ (ℕ->ℚ-preserves-order _ _ refl-≤))
        (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ n⁺)))
      0<diff)

isδFine-harmonic-partition : {a b : ℝ} -> (a<b : a < b) -> (n : Nat⁺) ->
  isδFine (ℚ->ℝ (1/ℕ n) * diff a b) (harmonic-partition a<b n)
isδFine-harmonic-partition {a} {b} a<b n⁺@(n , _) i = path-≤ p-width-path
  where

  p = harmonic-partition a<b n⁺
  module p = Partition p

  i-path : diff (ℚ->ℝ (ℕ->ℚ (Fin.i (inc-fin i))))
                (ℚ->ℝ (ℕ->ℚ (Fin.i (suc-fin i)))) == 1#
  i-path =
    sym ℚ->ℝ-preserves-diff >=>
    cong ℚ->ℝ (sym (ℤ->ℚ-preserves-diff _ _) >=>
               cong ℤ->ℚ (int.add1-extract-left >=> cong int.add1 +-inverse))

  p-width-path : p.width i == (ℚ->ℝ (1/ℕ n⁺)) * diff a b
  p-width-path =
    sym +-swap-diff >=>
    +-right +-inverse >=>
    +-right-zero >=>
    sym *-distrib-diff-right >=>
    *-left (sym *-distrib-diff-right >=>
            *-left i-path >=>
            *-left-one)
