{-# OPTIONS --cubical --safe --exact-split #-}

module nat.order.base where

open import base
open import nat
open import equality
open import hlevel
open import relation
open import functions
open import sigma.base
open import sum
open import truncation

_ℕ≤_ : Nat -> Nat -> Type₀
m ℕ≤ n = Σ[ x ∈ Nat ] x +' m == n

_ℕ<_ : Nat -> Nat -> Set
m ℕ< n = (suc m) ℕ≤ n

zero-≤ : {n : Nat} -> zero ℕ≤ n
zero-≤ {n} = (n , +'-right-zero)

suc-≤ : {m n : Nat} -> m ℕ≤ n -> suc m ℕ≤ suc n
suc-≤ (x , p) = (x , +'-right-suc >=> cong suc p)

zero-< : {n : Nat} -> zero ℕ< (suc n)
zero-< = suc-≤ zero-≤

zero-≮ : {n : Nat} -> ¬(n ℕ< zero)
zero-≮ (zero  , p) = zero-suc-absurd (sym p)
zero-≮ (suc _ , p) = zero-suc-absurd (sym p)

pred-≤ : {m n : Nat} -> m ℕ≤ n -> pred m ℕ≤ pred n
pred-≤ {m = zero}              _       = zero-≤
pred-≤ {m = suc _} {n = zero}  lt      = bot-elim (zero-≮ lt)
pred-≤ {m = suc _} {n = suc _} (x , p) = (x , cong pred (sym +'-right-suc >=> p))

right-suc-≤ : {m n : Nat} -> m ℕ≤ n -> m ℕ≤ (suc n)
right-suc-≤ (x , p) = suc x , cong suc p

isProp-ℕ≤ : {m n : Nat} -> isProp (m ℕ≤ n)
isProp-ℕ≤ (_ , p1) (_ , p2) =
  ΣProp-path (isSetNat _ _) (+'-right-injective (p1 >=> (sym p2)))
