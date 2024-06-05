{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.rational where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import commutative-monoid
open import equality
open import fraction.order
open import fraction.sign
open import functions
open import funext
open import hlevel
open import int
open import int.order using (≥0->NonNeg)
open import nat
open import nat.order
open import order
open import order.instances.rational
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.int
open import ordered-semiring.instances.int
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import sign
open import monoid
open import truncation

private
  int-reflects-< : {a b : ℕ} -> (int a) < (int b) -> a < b
  int-reflects-< {a} {b} ((suc i , _) , p) =
    (i , nonneg-injective (CommMonoidʰ.preserves-∙ int-+ʰ i (suc a) >=>
                           add1-extract-right >=> sym add1-extract-left >=> p))

  int-reflects-≤ : {a b : ℕ} -> (int a) ≤ (int b) -> a ≤ b
  int-reflects-≤ {a} {b} (i , p) =
    (i , nonneg-injective (CommMonoidʰ.preserves-∙ int-+ʰ i a >=> p))

  ℤ->ℚ-preserves-0≤ : (a : ℤ) -> 0# ≤ a -> 0# ≤ (ℤ->ℚ a)
  ℤ->ℚ-preserves-0≤ (nonneg a) 0≤a = ℕ->ℚ-preserves-≤ (int-reflects-≤ 0≤a)
  ℤ->ℚ-preserves-0≤ (neg a) 0≤a =
    bot-elim (int.NonNeg->¬Neg {neg a} (≥0->NonNeg 0≤a) Neg-a)
    where
    Neg-a : int.Neg (neg a)
    Neg-a = tt

  ℤ->ℚ-preserves-0< : (a : ℤ) -> 0# < a -> 0# < (ℤ->ℚ a)
  ℤ->ℚ-preserves-0< (nonneg a) 0<a = ℕ->ℚ-preserves-< (int-reflects-< 0<a)
  ℤ->ℚ-preserves-0< (neg a) 0<a =
    bot-elim (int.NonNeg->¬Neg {neg a} (≥0->NonNeg (weaken-< 0<a)) Neg-a)
    where
    Neg-a : int.Neg (neg a)
    Neg-a = tt


  ℤ->ℚ-preserves-≤ : (a b : ℤ) -> a ≤ b -> (ℤ->ℚ a) ≤ (ℤ->ℚ b)
  ℤ->ℚ-preserves-≤ a b (i , p) =
    trans-≤-= (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ (ℕ->ℚ-preserves-≤ zero-≤)))
              (sym (ℤ->ℚ-preserves-+ _ _) >=> cong ℤ->ℚ p)

  ℤ->ℚ-preserves-< : (a b : ℤ) -> a < b -> (ℤ->ℚ a) < (ℤ->ℚ b)
  ℤ->ℚ-preserves-< a b ((suc i , _) , p) =
    trans-<-= (trans-=-< (sym +-left-zero) (+₂-preserves-< (ℕ->ℚ-preserves-< zero-<)))
              (sym (ℤ->ℚ-preserves-+ _ _) >=> cong ℤ->ℚ p)

  ℚFinite : (q : ℚ) -> ∃[ n ∈ ℕ ] (q < ℕ->ℚ n)
  ℚFinite q = ∥-bind handle (ℚ->split-ℤ/ℕ q)
    where
    handle : Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d) ->
             ∃[ m ∈ ℕ ] (q < ℕ->ℚ m)
    handle (n , d , p) = handle2 (split-< 0# n)
      where
      handle2 : (0# < n) ⊎ (n ≤ 0#) -> ∃[ m ∈ ℕ ] (q < ℕ->ℚ m)
      handle2 (inj-r n≤0) =
        ∣ 1# , trans-=-< p (trans-≤-< (trans-≤-= (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ n 0# n≤0)
                                                                 (weaken-< (Pos-1/ℕ d)))
                                                 *-left-zero)
                                      Pos-1r) ∣
      handle2 (inj-l 0<n) = ∥-map handle3 (archimedean-property 0<n 0<1)
        where
        handle3 : Σ[ m ∈ ℕ ] (n < (ℕ->Semiring m * 1#)) ->
                  Σ[ m ∈ ℕ ] (q < ℕ->ℚ m)
        handle3 (m , n<m*1) =
          m , trans-≤-<
                (trans-=-≤ p (trans-≤-= (*₁-preserves-≤ (weaken-< (ℤ->ℚ-preserves-< _ _ 0<n))
                                                        (1/ℕ≤1 d))
                                        *-right-one))
                (trans-<-= (ℤ->ℚ-preserves-< _ _ n<m*1)
                           (cong ℤ->ℚ (*-right-one >=> ℕ->Semiring-ℤ-path m)))


  ℚFinite' : (q : ℚ) -> ∃[ n ∈ ℕ ] (q < ℕ->Semiring n)
  ℚFinite' = subst (\f -> (q : ℚ) -> ∃[ n ∈ ℕ ] (q < f n)) (sym (funExt ℕ->Semiring-ℚ-path))
                   ℚFinite

  prop : ArchimedeanPropertyⁱ ℚ
  prop {a} {b} 0<a 0<b = ∥-map (\ (n , lt) -> handle n lt) (ℚFinite' a/b)
    where
    inv-b : ℚInv b
    inv-b = Pos->Inv 0<b
    a/b : ℚ
    a/b = a * (r1/ b inv-b)
    module _ (n : ℕ) (a/b<n : a/b < ℕ->Semiring n) where
      handle : Σ[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
      handle = n , trans-=-< p (*₂-preserves-< a/b<n 0<b)
        where
        p = sym *-right-one >=>
            *-right (sym (r1/-inverse b inv-b)) >=>
            (sym *-assoc)

abstract
  instance
    ArchimedeanSemring-ℚ : ArchimedeanSemiringⁱ ℚ
    ArchimedeanSemring-ℚ = record { prop = prop }
