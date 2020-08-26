{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations where

open import base
open import commutative-monoid
open import equality
open import hlevel
open import nat
open import ring

import int


NatSemiring : Semiring Nat
NatSemiring = record
  { 0# = 0
  ; 1# = 1
  ; _+_ = _+'_
  ; _*_ = _*'_
  ; +-assoc = (\ {m} {n} {o} -> (+'-assoc {m} {n} {o}))
  ; +-commute = (\ {m} {n} -> (+'-commute {m} {n}))
  ; *-assoc = (\ {m} {n} {o} -> (*'-assoc {m} {n} {o}))
  ; *-commute = (\ {m} {n} -> (*'-commute {m} {n}))
  ; +-left-zero = refl
  ; *-left-zero = refl
  ; *-left-one = +'-right-zero
  ; *-distrib-+-right = (\ {m} {n} {o} -> *'-distrib-+' {m} {n} {o})
  ; isSetDomain = isSetNat
  }
module NatSemiring = Semiring NatSemiring

IntSemiring : Semiring int.Int
IntSemiring = record
  { 0# = (int.int 0)
  ; 1# = (int.int 1)
  ; _+_ = int._+_
  ; _*_ = int._*_
  ; +-assoc = (\ {m} {n} {o} -> (int.+-assoc {m} {n} {o}))
  ; +-commute = (\ {m} {n} -> (int.+-commute {m} {n}))
  ; *-assoc = (\ {m} {n} {o} -> (int.*-assoc {m} {n} {o}))
  ; *-commute = (\ {m} {n} -> (int.*-commute {m} {n}))
  ; +-left-zero = refl
  ; *-left-zero = refl
  ; *-left-one = int.+-right-zero
  ; *-distrib-+-right = (\ {m} {n} {o} -> int.*-distrib-+ {m} {n} {o})
  ; isSetDomain = int.isSetInt
  }
module IntSemiring = Semiring IntSemiring

IntRing : Ring int.Int
IntRing = record  {
  semiring = IntSemiring;
  -_ = int.-_;
  +-inverse = (\ {n} -> int.add-minus-zero {n}) }

^'ʰ : (x : Nat) -> CommMonoidʰᵉ NatSemiring.+-CommMonoid NatSemiring.*-CommMonoid (x ^'_)
^'ʰ x = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  preserves-∙ : (a b : Nat) -> (x ^' (a +' b)) == (x ^' a) *' (x ^' b)
  preserves-∙ zero    b = sym *'-left-one
  preserves-∙ (suc a) b =
    cong (x *'_) (preserves-∙ a b)
    >=> sym (*'-assoc {x} {x ^' a} {x ^' b})

module _ where
  open int
  ^ʰ : (x : Int) -> CommMonoidʰᵉ NatSemiring.+-CommMonoid IntSemiring.*-CommMonoid (x ^_)
  ^ʰ x = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    }
    where
    preserves-∙ : (a b : Nat) -> (x ^ (a +' b)) == (x ^ a) * (x ^ b)
    preserves-∙ zero    b = sym *-left-one
    preserves-∙ (suc a) b =
      cong (x *_) (preserves-∙ a b)
      >=> sym (*-assoc {x} {x ^ a} {x ^ b})


  int-+ʰ : CommMonoidʰᵉ NatSemiring.+-CommMonoid IntSemiring.+-CommMonoid  int
  int-+ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    }
    where
    preserves-∙ : (a b : Nat) -> (int (a +' b)) == (int a) + (int b)
    preserves-∙ zero    b = refl
    preserves-∙ (suc a) b =
      cong add1 (preserves-∙ a b)



ReaderSemiring : {ℓ₁ ℓ₂ : Level} {Domain : Type ℓ₁} -> (A : Type ℓ₂)
                 -> Semiring Domain -> Semiring (A -> Domain)
ReaderSemiring {Domain = Domain} A S = res
  where
  open Semiring S

  res : Semiring (A -> Domain)
  res = record
    { 0# = \a -> 0#
    ; 1# = \a -> 1#
    ; _+_ = (\ x y a -> (x a + y a))
    ; _*_ = (\ x y a -> (x a * y a))
    ; +-assoc = (\ {m} {n} {o} i a -> (+-assoc {m a} {n a} {o a}) i)
    ; +-commute = (\ {m} {n} i a -> (+-commute {m a} {n a} i))
    ; *-assoc = (\ {m} {n} {o} i a -> (*-assoc {m a} {n a} {o a} i))
    ; *-commute = (\ {m} {n} i a -> (*-commute {m a} {n a} i))
    ; +-left-zero = (\ {m} i a -> (+-left-zero {m a} i))
    ; *-left-zero = (\ {m} i a -> (*-left-zero {m a} i))
    ; *-left-one = (\ {m} i a -> (*-left-one {m a} i))
    ; *-distrib-+-right = (\ {m} {n} {o} i a -> (*-distrib-+-right {m a} {n a} {o a} i))
    ; isSetDomain = isSetΠ (\ _ -> isSetDomain)
    }


ReaderRing : {ℓ : Level} {Domain : Type ℓ} -> (A : Type ℓ) -> Ring Domain -> Ring (A -> Domain)
ReaderRing {Domain = Domain} A R = res
  where
  open Ring R

  res : Ring (A -> Domain)
  res = record  {
    semiring = (ReaderSemiring A semiring);
    -_ = (\ x a -> - x a);
    +-inverse = (\ {x} i a -> (+-inverse {x a} i)) }
