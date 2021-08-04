{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.abs where

open import base
open import equality
open import order
open import order.instances.rational
open import ordered-ring
open import ordered-ring.instances.rational
open import rational
open import rational.minmax
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.proper-interval
open import relation
open import ring
open import ring.implementations.rational
open import semiring


ImbalancedI : Pred Iℚ ℓ-zero
ImbalancedI (Iℚ-cons l u _) = (- l) ℚ≤ u


i-abs : Iℚ -> Iℚ
i-abs (Iℚ-cons l u l≤u) = (Iℚ-cons (maxℚ l 0r) (maxℚ (- l) u) lt)
  where
  LT = (maxℚ l 0r) ℚ≤ (maxℚ (- l) u)
  abstract
    lt : LT
    lt = handle (split-< l 0r)
      where
      handle : (l < 0r) ⊎ (0r ℚ≤ l) -> LT
      handle (inj-l l<0) =
        subst (_ℚ≤ (maxℚ (- l) u))
          (sym (maxℚ-right l 0r (inj-l l<0)))
          (trans-ℚ≤ {0r} (inj-l (minus-flips-< l 0r l<0)) (maxℚ-≤-left (- l) u))
      handle (inj-r 0≤l) =
        subst2 (_ℚ≤_) (sym (maxℚ-left l 0r 0≤l)) (sym (maxℚ-right (- l) u -l≤u)) l≤u
        where
        -l≤0 : (- l) ℚ≤ 0r
        -l≤0 = (r--flips-≤ 0r l 0≤l)
        -l≤u : (- l) ℚ≤ u
        -l≤u = trans-ℚ≤ { - l} (trans-ℚ≤ { - l}-l≤0 0≤l) l≤u
