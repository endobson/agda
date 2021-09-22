{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import additive-group.instances.reader
open import base
open import commutative-monoid
open import equality
open import funext
open import hlevel
open import nat
open import ring
open import semiring

import int
open int using
 ( Int
 ; int
 ; ℕ->ℤ
 ; _^_
 ; ^-right-zero
 ; ^-right-suc
 ; add1
 ; add1-extract-left
 ; add1-extract-*
 )

instance
  NatSemiring : Semiring AdditiveCommMonoid-Nat
  NatSemiring = record
    { 1# = 1
    ; _*_ = _*'_
    ; *-assoc = (\ {m} {n} {o} -> (*'-assoc {m} {n} {o}))
    ; *-commute = (\ {m} {n} -> (*'-commute {m} {n}))
    ; *-left-zero = refl
    ; *-left-one = +'-right-zero
    ; *-distrib-+-right = (\ {m} {n} {o} -> *'-distrib-+' {m} {n} {o})
    ; isSet-Domain = isSetNat
    }
module NatSemiring = Semiring NatSemiring

instance
  IntSemiring : Semiring AdditiveCommMonoid-Int
  IntSemiring = record
    { 1# = (int.int 1)
    ; _*_ = int._*_
    ; *-assoc = (\ {m} {n} {o} -> (int.*-assoc {m} {n} {o}))
    ; *-commute = (\ {m} {n} -> (int.*-commute {m} {n}))
    ; *-left-zero = int.*-left-zero
    ; *-left-one = int.*-left-one
    ; *-distrib-+-right = (\ {m} {n} {o} -> int.*-distrib-+ {m} {n} {o})
    ; isSet-Domain = int.isSetInt
    }
module IntSemiring = Semiring IntSemiring

instance
  IntRing : Ring IntSemiring
  IntRing = record  {
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
  ^ʰ : (x : Int) -> CommMonoidʰᵉ NatSemiring.+-CommMonoid IntSemiring.*-CommMonoid (x ^_)
  ^ʰ x = record
    { preserves-ε = ^-right-zero
    ; preserves-∙ = preserves-∙
    }
    where
    preserves-∙ : (a b : Nat) -> (x ^ (a +' b)) == (x ^ a) * (x ^ b)
    preserves-∙ zero    b = sym (cong (_* (x ^ b)) ^-right-zero >=> *-left-one)
    preserves-∙ (suc a) b =
      ^-right-suc
      >=> cong (x *_) (preserves-∙ a b)
      >=> sym (int.*-assoc {x} {x ^ a} {x ^ b})
      >=> sym (cong (_* _) ^-right-suc)


  int-+ʰ : CommMonoidʰᵉ NatSemiring.+-CommMonoid IntSemiring.+-CommMonoid  int
  int-+ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    }
    where
    preserves-∙ : (a b : Nat) -> (int (a +' b)) == (int a) + (int b)
    preserves-∙ zero    b = sym +-left-zero
    preserves-∙ (suc a) b =
      cong add1 (preserves-∙ a b) >=> sym add1-extract-left

  int-*ʰ : CommMonoidʰᵉ NatSemiring.*-CommMonoid IntSemiring.*-CommMonoid  int
  int-*ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    }
    where
    preserves-∙ : (a b : Nat) -> (int (a *' b)) == (int a) * (int b)
    preserves-∙ zero    b = sym *-left-zero
    preserves-∙ (suc a) b =
      begin
        int ((suc a) *' b)
      ==<>
        int (b +' (a *' b))
      ==< CommMonoidʰ.preserves-∙ int-+ʰ b (a *' b) >
        int b + int (a *' b)
      ==< cong (int b +_) (preserves-∙ a b) >
        int b + ((int a) * (int b))
      ==< sym (add1-extract-* {int a} {int b}) >
        (int (suc a)) * (int b)
      end

  Semiringʰ-ℕ->ℤ : Semiringʰ ℕ->ℤ
  Semiringʰ-ℕ->ℤ = record
    { preserves-1# = CommMonoidʰ.preserves-ε int-*ʰ
    ; preserves-+ = CommMonoidʰ.preserves-∙ int-+ʰ
    ; preserves-* = CommMonoidʰ.preserves-∙ int-*ʰ
    }



ReaderSemiring : {ℓ₁ ℓ₂ : Level} {Domain : Type ℓ₁} {ACM : AdditiveCommMonoid Domain} ->
                 (A : Type ℓ₂) -> Semiring ACM ->
                 Semiring (AdditiveCommMonoid-Reader ACM A)
ReaderSemiring {Domain = Domain} {ACM = ACM} A S = res
  where
  private
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


ReaderRing : {ℓ : Level} {Domain : Type ℓ} {ACM : AdditiveCommMonoid Domain} {S : Semiring ACM} ->
             (A : Type ℓ) -> Ring S -> Ring (ReaderSemiring A S)
ReaderRing {Domain = Domain} {ACM} {S} A R = res
  where
  instance
    IR = R

  res : Ring (ReaderSemiring A S)
  res = record  {
    -_ = (\ x a -> - x a);
    +-inverse = (\ {x} i a -> (Ring.+-inverse R {x a} i)) }
