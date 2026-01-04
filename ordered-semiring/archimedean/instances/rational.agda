{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.rational where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import fraction.order
open import fraction.sign
open import functions
open import funext
open import hlevel
open import int.base
open import monoid
open import nat
open import nat.order
open import order
open import order.instances.int
open import order.instances.nat
open import order.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.int
open import ordered-semiring.instances.int
open import ordered-semiring.instances.rational
open import ordered-semiring.natural-reciprocal
open import rational
open import rational.order
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import semiring.natural-reciprocal
open import sign
open import truncation

private
  ℚFinite : (q : ℚ) -> ∃[ n ∈ ℕ ] (q < ℕ->ℚ n)
  ℚFinite q = ∥-bind handle (ℚ->split-ℤ/ℕ q)
    where
    handle : Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d) ->
             ∃[ m ∈ ℕ ] (q < ℕ->ℚ m)
    handle (n , d , p) = handle2 (split-< 0# n)
      where
      handle2 : (0# < n) ⊎ (n ≤ 0#) -> ∃[ m ∈ ℕ ] (q < ℕ->ℚ m)
      handle2 (inj-r n≤0) =
        ∣ 1# , trans-=-< p (trans-≤-< (trans-≤-= (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ n≤0)
                                                                 (weaken-< (Pos-1/ℕ d)))
                                                 *-left-zero)
                                      Pos-1r) ∣
      handle2 (inj-l 0<n) = ∥-map handle3 (archimedean-property 0<n 0<1)
        where
        handle3 : Σ[ m ∈ ℕ ] (n < (ℕ->ℤ m * 1#)) ->
                  Σ[ m ∈ ℕ ] (q < ℕ->ℚ m)
        handle3 (m , n<m*1) =
          m , trans-≤-<
                (trans-=-≤ p (trans-≤-= (*₁-preserves-≤ (weaken-< (ℤ->ℚ-preserves-< 0<n))
                                                        (1/ℕ≤1 d))
                                        *-right-one))
                (trans-<-= (ℤ->ℚ-preserves-< n<m*1)
                           (cong ℤ->ℚ *-right-one))

  prop : ArchimedeanPropertyⁱ ℚ
  prop {a} {b} 0<a 0<b = ∥-map (\ (n , lt) -> handle n lt) (ℚFinite a/b)
    where
    inv-b : ℚInv b
    inv-b = Pos->Inv 0<b
    a/b : ℚ
    a/b = a * (r1/ b inv-b)
    module _ (n : ℕ) (a/b<n : a/b < ℕ->ℚ n) where
      handle : Σ[ n ∈ ℕ ] (a < (ℕ->ℚ n * b))
      handle = n , trans-=-< p (*₂-preserves-< a/b<n 0<b)
        where
        p = sym *-right-one >=>
            *-right (sym (r1/-inverse b inv-b)) >=>
            (sym *-assoc)

abstract
  instance
    ArchimedeanSemring-ℚ : ArchimedeanSemiringⁱ ℚ
    ArchimedeanSemring-ℚ = record { prop = prop }
