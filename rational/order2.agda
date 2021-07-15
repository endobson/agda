{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order2 where

open import abs
open import base
open import equality
open import fraction.sign
open import fraction.order
open import hlevel
open import isomorphism
open import order
open import order.instances.int
open import rational
open import relation
open import ring
open import ring.implementations.rational
open import ring.implementations
open import semiring
open import set-quotient
open import sigma
open import sign
open import sign.instances.fraction
open import truncation
open import univalence

private
  ℚ<-full : ℚ -> ℚ -> hProp ℓ-zero
  ℚ<-full = RationalElim.elim2 (\_ _ -> isSet-hProp) val preserved₁ preserved₂
    where
    val : ℚ' -> ℚ' -> hProp ℓ-zero
    val q r = q ℚ'< r , isProp-ℚ'<
    preserved₁ : (a b c : ℚ') -> (a r~ b) -> val a c == val b c
    preserved₁ a b c a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (a ℚ'< c) (b ℚ'< c)
      i .fun a<c = r~-preserves-<₁ a<c a~b
      i .inv b<c = r~-preserves-<₁ b<c (sym a~b)
      i .rightInv _ = isProp-ℚ'< _ _
      i .leftInv _ = isProp-ℚ'< _ _
    preserved₂ : (a b c : ℚ') -> (b r~ c) -> val a b == val a c
    preserved₂ a b c b~c = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (a ℚ'< b) (a ℚ'< c)
      i .fun a<b = r~-preserves-<₂ a<b b~c
      i .inv a<c = r~-preserves-<₂ a<c (sym b~c)
      i .rightInv _ = isProp-ℚ'< _ _
      i .leftInv _ = isProp-ℚ'< _ _

  ℚ<-rawᵉ : ℚ -> ℚ -> Type₀
  ℚ<-rawᵉ q r = ⟨ ℚ<-full q r ⟩

  abstract
    ℚ<-raw : ℚ -> ℚ -> Type₀
    ℚ<-raw = ℚ<-rawᵉ

record _ℚ<_ (q : ℚ) (r : ℚ) : Type₀ where
  constructor ℚ<-cons
  field
    v : ℚ<-raw q r
