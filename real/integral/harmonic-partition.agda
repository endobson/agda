{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.harmonic-partition where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.real
open import base
open import equality
open import fin
open import integral-domain.instances.real
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import ordered-integral-domain
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.rational
open import real.heyting-field
open import real.integral.partition
open import real.order
open import real.rational
open import ring
open import ring.implementations.real
open import semiring
open import truncation

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
  u<u _ =
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

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)


private
  small-1/ℕ-ℝ : (x : ℝ⁺) -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < ⟨ x ⟩)
  small-1/ℕ-ℝ (x , 0<x) = ∥-bind handle 0<x
    where
    handle : 0# ℝ<' x -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
    handle (ℝ<'-cons q 0<q q<x) = ∥-map handle2 (small-1/ℕ (q , U->ℚ< 0<q))
      where
      handle2 : Σ[ m ∈ Nat⁺ ] (1/ℕ m) < q ->
                Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
      handle2 (m , 1/m<q) = m , ∣ (ℝ<'-cons q (ℚ<->U 1/m<q) q<x) ∣

  ∃δFinePartition' : {a b : ℝ} -> a < b -> (δ : ℝ⁺) -> ∃ (Partition a b) (isδFine (⟨ δ ⟩ * diff a b))
  ∃δFinePartition' {a} {b} a<b (δ , 0<δ) = ∥-map handle (small-1/ℕ-ℝ (δ , 0<δ))
    where
    handle : Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < δ) ->
             Σ (Partition a b) (isδFine (δ * diff a b))
    handle (n⁺ , 1/n<δ) =
      p , (weaken-isδFine (*₂-preserves-≤ (weaken-< 1/n<δ) 0≤ab) p δ-p)
      where
      p = harmonic-partition a<b n⁺
      δ-p : isδFine (ℚ->ℝ (1/ℕ n⁺) * diff a b) p
      δ-p = isδFine-harmonic-partition a<b n⁺

      0≤ab = weaken-< (trans-=-< (sym +-inverse) (+₂-preserves-< a<b))


∃δFinePartition : {a b : ℝ} -> a < b -> (δ : ℝ⁺) -> ∃ (Partition a b) (isδFine ⟨ δ ⟩)
∃δFinePartition {a} {b} a<b (δ , 0<δ) =
  ∥-bind handle (comparison-< 0# ab 1# 0<1)
  where
  ab = diff a b
  handle : ((0# < ab) ⊎ (ab < 1#)) -> ∃ (Partition a b) (isδFine δ)
  handle (inj-l 0<ab) =
    subst (\δ -> ∃ (Partition a b) (isδFine δ))
          (*-assoc >=> *-right (ℝ1/-inverse ab (inj-r 0<ab)) >=> *-right-one)
          (∃δFinePartition' a<b (δ/ab , 0<δ/ab))
    where
    1/ab = ℝ1/ ab (inj-r 0<ab)
    0<1/ab : 0# < 1/ab
    0<1/ab =
      *₂-reflects-<
        (subst2 _<_ (sym *-left-zero) (sym (ℝ1/-inverse ab (inj-r 0<ab))) 0<1)
        0<ab
    δ/ab = δ * 1/ab
    0<δ/ab = *-preserves-0< 0<δ 0<1/ab
  handle (inj-r ab<1) = ∥-map handle2 (∃δFinePartition' a<b (δ , 0<δ))
    where
    handle2 : Σ (Partition a b) (isδFine (δ * ab)) ->
              Σ (Partition a b) (isδFine δ)
    handle2 (p , δab-p) = p , weaken-isδFine δab≤δ p δab-p
      where
      δab≤δ = trans-≤-= (weaken-< (*₁-preserves-< 0<δ ab<1)) *-right-one
