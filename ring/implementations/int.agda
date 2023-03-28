{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.int where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import additive-group.instances.reader
open import base
open import commutative-monoid
open import equality
open import hlevel
open import nat
open import ring
open import semiring
open import semiring.instances.nat


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
instance
  IntRing : Ring IntSemiring AdditiveGroup-Int
  IntRing = record  {}

private
  module NatSemiring = Semiring NatSemiring
  module IntSemiring = Semiring IntSemiring

^'ʰ : (x : Nat) -> CommMonoidʰᵉ NatSemiring.+-CommMonoid NatSemiring.*-CommMonoid (x ^'_)
^'ʰ x = record
  { monoidʰ = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    }
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
    { monoidʰ = record
      { preserves-ε = ^-right-zero
      ; preserves-∙ = preserves-∙
      }
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
    { monoidʰ = record
      { preserves-ε = refl
      ; preserves-∙ = preserves-∙
      }
    }
    where
    preserves-∙ : (a b : Nat) -> (int (a +' b)) == (int a) + (int b)
    preserves-∙ zero    b = sym +-left-zero
    preserves-∙ (suc a) b =
      cong add1 (preserves-∙ a b) >=> sym add1-extract-left

  int-*ʰ : CommMonoidʰᵉ NatSemiring.*-CommMonoid IntSemiring.*-CommMonoid  int
  int-*ʰ = record
    { monoidʰ = record
      { preserves-ε = refl
      ; preserves-∙ = preserves-∙
      }
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
    { +ʰ = CommMonoidʰ.monoidʰ int-+ʰ
    ; *ʰ = CommMonoidʰ.monoidʰ int-*ʰ
    }
