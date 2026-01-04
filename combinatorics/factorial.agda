{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.factorial where

open import additive-group.instances.nat
open import base
open import equality
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-ring
open import ordered-additive-group.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import semiring
open import semiring.exponentiation
open import semiring.instances.nat

factorial : ℕ -> ℕ
factorial zero = 1#
factorial (suc n) = (suc n) * factorial n

private
  0<factorial : (n : ℕ) -> 0 < factorial n
  0<factorial zero = zero-<
  0<factorial (suc n) = *-preserves-0< (zero-< {n}) (0<factorial n)

factorial⁺ : ℕ -> Nat⁺
factorial⁺ n = factorial n , pf n
  where
  pf : (n : ℕ) -> Pos' (factorial n)
  pf zero = tt
  pf (suc n) = *'-Pos'-Pos' {suc n} {factorial n} tt (pf n)

opaque
  -- 1 2 4 8 16 32
  -- 1 1 2 6 24 120
  2^n<factorial : (n : ℕ) -> n ≥ 4 ->  (2 ^ℕ n) < factorial n
  2^n<factorial zero                   0≥4 = bot-elim (zero-≮ 0≥4)
  2^n<factorial (suc zero)             1≥4 = bot-elim (zero-≮ (pred-≤ 1≥4))
  2^n<factorial (suc (suc zero))       2≥4 = bot-elim (zero-≮ (pred-≤ (pred-≤ 2≥4)))
  2^n<factorial (suc (suc (suc zero))) 3≥4 = bot-elim (zero-≮ (pred-≤ (pred-≤ (pred-≤ 3≥4))))
  2^n<factorial (suc (suc (suc (suc zero)))) 4≥4 =
    suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (
      suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ zero-≤))))))))))))))))
  2^n<factorial sn+4@(suc n+4@(suc (suc (suc (suc n))))) sn+4≥4 =
    trans-< (*₁-preserves-< 0<2 (2^n<factorial n+4 (suc-≤ (suc-≤ (suc-≤ (suc-≤ zero-≤))))))
            (*₂-preserves-< 2<sn+4 (0<factorial n+4))
    where
    2<sn+4 : 2 < sn+4
    2<sn+4 = suc-≤ (suc-≤ (suc-≤ zero-≤))


  -- 1 2 4 8 16
  -- 1 2 6 24 120
  2^n≤factorial-suc : (n : ℕ) -> (2 ^ℕ n) ≤ factorial (suc n)
  2^n≤factorial-suc zero = refl-≤
  2^n≤factorial-suc (suc zero) = refl-≤
  2^n≤factorial-suc (suc (suc n)) =
    trans-≤ (*₁-preserves-≤ 0≤2 (2^n≤factorial-suc (suc n)))
            (*₂-preserves-≤ 2≤sssn (weaken-< (0<factorial (suc (suc n)))))
    where
    0≤2 : 0 ≤ 2
    0≤2 = zero-≤

    2≤sssn : 2 ≤ (suc (suc (suc n)))
    2≤sssn = suc-≤ (suc-≤ zero-≤)
