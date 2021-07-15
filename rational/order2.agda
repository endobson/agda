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
open import sum
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

    isProp-ℚ<-raw : (q r : ℚ) -> isProp (ℚ<-raw q r)
    isProp-ℚ<-raw q r = snd (ℚ<-full q r)

    ℚ<-raw-eval : {q r : ℚ} -> ℚ<-raw q r == ℚ<-rawᵉ q r
    ℚ<-raw-eval = refl

  ℚ≤-full : ℚ -> ℚ -> hProp ℓ-zero
  ℚ≤-full = RationalElim.elim2 (\_ _ -> isSet-hProp) val preserved₁ preserved₂
    where
    val : ℚ' -> ℚ' -> hProp ℓ-zero
    val q r = q ℚ'≤ r , isProp-ℚ'≤
    preserved₁ : (a b c : ℚ') -> (a r~ b) -> val a c == val b c
    preserved₁ a b c a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (a ℚ'≤ c) (b ℚ'≤ c)
      i .fun a≤c = r~-preserves-≤₁ a≤c a~b
      i .inv b≤c = r~-preserves-≤₁ b≤c (sym a~b)
      i .rightInv _ = isProp-ℚ'≤ _ _
      i .leftInv _ = isProp-ℚ'≤ _ _
    preserved₂ : (a b c : ℚ') -> (b r~ c) -> val a b == val a c
    preserved₂ a b c b~c = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (a ℚ'≤ b) (a ℚ'≤ c)
      i .fun a≤b = r~-preserves-≤₂ a≤b b~c
      i .inv a≤c = r~-preserves-≤₂ a≤c (sym b~c)
      i .rightInv _ = isProp-ℚ'≤ _ _
      i .leftInv _ = isProp-ℚ'≤ _ _

  ℚ≤-rawᵉ : ℚ -> ℚ -> Type₀
  ℚ≤-rawᵉ q r = ⟨ ℚ≤-full q r ⟩

  abstract
    ℚ≤-raw : ℚ -> ℚ -> Type₀
    ℚ≤-raw = ℚ≤-rawᵉ

    isProp-ℚ≤-raw : (q r : ℚ) -> isProp (ℚ≤-raw q r)
    isProp-ℚ≤-raw q r = snd (ℚ≤-full q r)

    ℚ≤-raw-eval : {q r : ℚ} -> ℚ≤-raw q r == ℚ≤-rawᵉ q r
    ℚ≤-raw-eval = refl


record _ℚ<_ (q : ℚ) (r : ℚ) : Type₀ where
  constructor ℚ<-cons
  field
    v : ℚ<-raw q r

record _ℚ≤_ (q : ℚ) (r : ℚ) : Type₀ where
  constructor ℚ≤-cons
  field
    v : ℚ≤-raw q r

abstract
  isProp-ℚ< : {a b : Rational} -> isProp (a ℚ< b)
  isProp-ℚ< {a} {b} (ℚ<-cons a<b1) (ℚ<-cons a<b2) =
    cong ℚ<-cons (isProp-ℚ<-raw a b a<b1 a<b2)

  isProp-ℚ≤ : {a b : Rational} -> isProp (a ℚ≤ b)
  isProp-ℚ≤ {a} {b} (ℚ≤-cons a≤b1) (ℚ≤-cons a≤b2) =
    cong ℚ≤-cons (isProp-ℚ≤-raw a b a≤b1 a≤b2)

  irrefl-ℚ< : Irreflexive _ℚ<_
  irrefl-ℚ< {a} (ℚ<-cons a<a) =
    RationalElim.elimProp
      {C = (\r -> ℚ<-rawᵉ r r -> Bot)}
      (\_ -> isPropΠ (\_ -> isPropBot))
      (\r r<r -> (irrefl-ℚ'< {r} r<r)) a a<a

  trans-ℚ< : Transitive _ℚ<_
  trans-ℚ< {a} {b} {c} (ℚ<-cons a<b) (ℚ<-cons b<c) =
    RationalElim.elimProp3
      {C3 = (\a b c -> ℚ<-raw a b -> ℚ<-raw b c -> a ℚ< c)}
      (\_ _ _ -> isPropΠ2 (\_ _ -> isProp-ℚ<))
      (\a b c a<b b<c -> ℚ<-cons (trans-ℚ'< a<b b<c))
      a b c a<b b<c

  asym-ℚ< : Asymmetric _ℚ<_
  asym-ℚ< lt1 lt2 = irrefl-ℚ< (trans-ℚ< lt1 lt2)

  connected-ℚ< : Connected _ℚ<_
  connected-ℚ< {a} {b} ¬a<b ¬b<a =
    RationalElim.elimProp2
      {C2 = (\a b -> ¬ (ℚ<-raw a b) -> ¬ (ℚ<-raw b a) -> a == b)}
      (\_ _ -> isPropΠ2 (\_ _ -> isSetRational _ _))
      (\a b ¬a<b ¬b<a -> eq/ _ _ (connected~-ℚ'< ¬a<b ¬b<a))
      a b (\a<b -> ¬a<b (ℚ<-cons a<b)) (\b<a -> ¬b<a (ℚ<-cons b<a))

  comparison-ℚ< : Comparison _ℚ<_
  comparison-ℚ< a b c (ℚ<-cons a<c) =
    RationalElim.elimProp3
      {C3 = (\a b c -> ℚ<-raw a c -> ∥ (a ℚ< b) ⊎ (b ℚ< c) ∥)}
      (\_ _ _ -> isPropΠ (\_ -> squash))
      compare
      a b c a<c
    where
    compare : (a b c : ℚ') -> ℚ<-raw [ a ] [ c ] -> ∥ ([ a ] ℚ< [ b ]) ⊎ ([ b ] ℚ< [ c ]) ∥
    compare a b c a<c = ∥-map (⊎-map ℚ<-cons ℚ<-cons) (comparison-ℚ'< a b c a<c)

instance
  LinearOrderStr-ℚ : LinearOrderStr ℚ ℓ-zero
  LinearOrderStr-ℚ = record
    { _<_ = _ℚ<_
    ; isProp-< = \_ _ -> isProp-ℚ<
    ; irrefl-< = irrefl-ℚ<
    ; trans-< = trans-ℚ<
    ; connected-< = connected-ℚ<
    ; comparison-< = comparison-ℚ<
    }
