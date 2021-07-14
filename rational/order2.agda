{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order2 where

open import abs
open import base
open import equality
open import fraction.sign
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


record _ℚ'<_ (q : ℚ') (r : ℚ') : Type₀ where
  constructor ℚ'<-cons
  private
    qn = Rational'.numerator q
    qd = Rational'.denominator q
    rn = Rational'.numerator r
    rd = Rational'.denominator r

  field
    v : (qn * rd) < (rn * qd)

isProp-ℚ'< : {q r : ℚ'} -> isProp (q ℚ'< r)
isProp-ℚ'< (ℚ'<-cons lt1) (ℚ'<-cons lt2) = cong ℚ'<-cons (isProp-< _ _ lt1 lt2)

-- private
--
--   r~-preserves-<₁ : {q r s : Rational'} -> q ℚ'< r -> q r~ s -> s ℚ'< r
--   r~-preserves-<₁ {q} {r} {s} (ℚ'<-cons lt) q~s = (ℚ'<-cons snrd<rnsd)
--     where
--     qn = Rational'.numerator q
--     qd = Rational'.denominator q
--     rn = Rational'.numerator r
--     rd = Rational'.denominator r
--     sn = Rational'.numerator s
--     sd = Rational'.denominator s
--
--     qnrd<rnqd : (qn * rd) < (rn * qd)
--     qnrd<rnqd = lt
--
--     qnsd=snqd : (qn * sd) == (sn * qd)
--     qnsd=snqd = q~s
--
--     snrd<rnsd : (sn * rd) < (rn * sd)
--     snrd<rnsd = ?
--
--
--   r~-preserves-<₂ : {q1 q2 r : Rational'} -> r ℚ'< q1 -> q1 r~ q2 -> r ℚ'< q2
--   r~-preserves-<₂ = ?
--
--
--   ℚ<-full : ℚ -> ℚ -> hProp ℓ-zero
--   ℚ<-full = RationalElim.elim2 (\_ _ -> isSet-hProp) val preserved₁ preserved₂
--     where
--     val : ℚ' -> ℚ' -> hProp ℓ-zero
--     val q r = q ℚ'< r , isProp-ℚ'<
--     preserved₁ : (a b c : ℚ') -> (a r~ b) -> val a c == val b c
--     preserved₁ a b c a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
--       where
--       open Iso
--       i : Iso (a ℚ'< c) (b ℚ'< c)
--       i .fun a<c = r~-preserves-<₁ a<c a~b
--       i .inv b<c = r~-preserves-<₁ b<c (sym a~b)
--       i .rightInv _ = isProp-ℚ'< _ _
--       i .leftInv _ = isProp-ℚ'< _ _
--     preserved₂ : (a b c : ℚ') -> (b r~ c) -> val a b == val a c
--     preserved₂ a b c b~c = ΣProp-path isProp-isProp (ua (isoToEquiv i))
--       where
--       open Iso
--       i : Iso (a ℚ'< b) (a ℚ'< c)
--       i .fun a<b = r~-preserves-<₂ a<b b~c
--       i .inv a<c = r~-preserves-<₂ a<c (sym b~c)
--       i .rightInv _ = isProp-ℚ'< _ _
--       i .leftInv _ = isProp-ℚ'< _ _
--
--   ℚ<-rawᵉ : ℚ -> ℚ -> Type₀
--   ℚ<-rawᵉ q r = ⟨ ℚ<-full q r ⟩
--
--   abstract
--     ℚ<-raw : ℚ -> ℚ -> Type₀
--     ℚ<-raw = ℚ<-rawᵉ
--
-- record _ℚ<_ (q : ℚ) (r : ℚ) : Type₀ where
--   constructor ℚ<-cons
--   field
--     v : ℚ<-raw q r
