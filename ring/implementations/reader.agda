{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.reader where

open import additive-group
open import additive-group.instances.reader
open import base
open import hlevel
open import ring
open import semiring

ReaderSemiring : {ℓ₁ ℓ₂ : Level} {Domain : Type ℓ₁} {ACM : AdditiveCommMonoid Domain} ->
                 (A : Type ℓ₂) -> Semiring ACM ->
                 Semiring (AdditiveCommMonoid-Reader ACM A)
ReaderSemiring {Domain = Domain} {ACM = ACM} A S = res
  where
  module S = Semiring S

  res : Semiring (AdditiveCommMonoid-Reader ACM A)
  res = record
    { 1# = \a -> S.1#
    ; _*_ = (\ x y a -> (x a S.* y a))
    ; *-assoc = (\ {m} {n} {o} i a -> (S.*-assoc {m a} {n a} {o a} i))
    ; *-commute = (\ {m} {n} i a -> (S.*-commute {m a} {n a} i))
    ; *-left-zero = (\ {m} i a -> (S.*-left-zero {m a} i))
    ; *-left-one = (\ {m} i a -> (S.*-left-one {m a} i))
    ; *-distrib-+-right = (\ {m} {n} {o} i a -> (S.*-distrib-+-right {m a} {n a} {o a} i))
    ; isSet-Domain = isSetΠ (\ _ -> S.isSet-Domain)
    }


ReaderRing : {ℓ : Level} {Domain : Type ℓ} {ACM : AdditiveCommMonoid Domain} {S : Semiring ACM}
             {AG : AdditiveGroup ACM} ->
             (A : Type ℓ) -> Ring S AG -> Ring (ReaderSemiring A S) (AdditiveGroup-Reader AG A)
ReaderRing {Domain = Domain} {ACM} {S} {AG} A R = record {}
