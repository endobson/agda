{-# OPTIONS --cubical --safe --exact-split #-}

module factorial where

open import base
open import equality
open import nat
open import ring.implementations
open import semiring
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-ring
open import ordered-semiring.instances.nat

factorial : ℕ -> ℕ
factorial zero = 1#
factorial (suc n) = (suc n) * factorial n

private
  0<factorial : (n : ℕ) -> 0 < factorial n
  0<factorial zero = zero-<
  0<factorial (suc n) = *-preserves-0< (zero-< {n}) (0<factorial n)

factorial⁺ : ℕ -> Nat⁺
factorial⁺ n = factorial n , <->Pos' (0<factorial n)

-- 1 2 4 8 16 32
-- 1 1 2 6 24 120
2^n<factorial : (n : ℕ) -> n ≥ 4 ->  (2 ^' n) < factorial n
2^n<factorial zero                   0≥4 = bot-elim (zero-≮ 0≥4)
2^n<factorial (suc zero)             1≥4 = bot-elim (zero-≮ (pred-≤ 1≥4))
2^n<factorial (suc (suc zero))       2≥4 = bot-elim (zero-≮ (pred-≤ (pred-≤ 2≥4)))
2^n<factorial (suc (suc (suc zero))) 3≥4 = bot-elim (zero-≮ (pred-≤ (pred-≤ (pred-≤ 3≥4))))
2^n<factorial (suc (suc (suc (suc zero)))) 4≥4 = 
  suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (
    suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ (suc-≤ zero-≤))))))))))))))))
2^n<factorial sn+4@(suc n+4@(suc (suc (suc (suc n))))) sn+4≥4 = 
  trans-< (*-left-<⁺ 0<2 (2^n<factorial n+4 (suc-≤ (suc-≤ (suc-≤ (suc-≤ zero-≤)))))) 
          (*-right-<⁺ (0<factorial n+4) 2<sn+4)
  where
  2<sn+4 : 2 < sn+4
  2<sn+4 = suc-≤ (suc-≤ (suc-≤ zero-≤))
  0<2 : 0 < 2
  0<2 = (suc-≤ zero-≤)

-- 2^n<factorial (suc (suc zero)) 1≥2 = 
--   subst2 _≤_ refl  refl-≤
--   where
--   p : factorial 2 == 
--   p = ?

