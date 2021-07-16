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
open import ordered-semiring
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

Posℚ : Pred ℚ ℓ-zero
Posℚ q = 0r < q
Negℚ : Pred ℚ ℓ-zero
Negℚ q = q < 0r
Zeroℚ : Pred ℚ ℓ-zero
Zeroℚ q = q == 0r

private
  isSignℚ : REL Sign ℚ ℓ-zero
  isSignℚ pos-sign = Posℚ
  isSignℚ zero-sign = Zeroℚ
  isSignℚ neg-sign = Negℚ

  abstract
    isProp-isSignℚ : (s : Sign) (q : ℚ) -> isProp (isSignℚ s q)
    isProp-isSignℚ pos-sign _ = isProp-< _ _
    isProp-isSignℚ zero-sign _ = isSetRational _ _
    isProp-isSignℚ neg-sign _ = isProp-< _ _

    isSignℚ-unique : (q : ℚ) (s1 s2 : Sign) -> (isSignℚ s1 q) -> (isSignℚ s2 q) -> s1 == s2
    isSignℚ-unique q pos-sign  pos-sign  s1q s2q = refl
    isSignℚ-unique q pos-sign  zero-sign s1q s2q = bot-elim (irrefl-< (subst (0r <_) s2q s1q))
    isSignℚ-unique q pos-sign  neg-sign  s1q s2q = bot-elim (asym-< s1q s2q)
    isSignℚ-unique q zero-sign pos-sign  s1q s2q = bot-elim (irrefl-< (subst (0r <_) s1q s2q))
    isSignℚ-unique q zero-sign zero-sign s1q s2q = refl
    isSignℚ-unique q zero-sign neg-sign  s1q s2q = bot-elim (irrefl-< (subst (_< 0r) s1q s2q))
    isSignℚ-unique q neg-sign  pos-sign  s1q s2q = bot-elim (asym-< s1q s2q)
    isSignℚ-unique q neg-sign  zero-sign s1q s2q = bot-elim (irrefl-< (subst (_< 0r) s2q s1q))
    isSignℚ-unique q neg-sign  neg-sign  s1q s2q = refl

instance
  SignStr-ℚ : SignStr ℚ ℓ-zero
  SignStr-ℚ = record
    { isSign = isSignℚ
    ; isProp-isSign = isProp-isSignℚ
    ; isSign-unique = isSignℚ-unique
    }

ℚ⁺ : Type₀
ℚ⁺ = Σ ℚ Pos
ℚ⁻ : Type₀
ℚ⁻ = Σ ℚ Neg

ℚ⁰⁺ : Type₀
ℚ⁰⁺ = Σ ℚ NonNeg
ℚ⁰⁻ : Type₀
ℚ⁰⁻ = Σ ℚ NonPos

abstract
  Zero-0r : Zero 0r
  Zero-0r = refl

  Pos->Inv : {q : ℚ} -> Pos q -> ℚInv q
  Pos->Inv p = NonZero->¬Zero (inj-l p)

  Neg->Inv : {q : ℚ} -> Neg q -> ℚInv q
  Neg->Inv p = NonZero->¬Zero (inj-r p)

abstract
  r+₁-preserves-< : (a b c : ℚ) -> b < c -> (a + b) < (a + c)
  r+₁-preserves-< a b c (ℚ<-cons b<c) =
    RationalElim.elimProp3
      {C3 = \a b c -> ℚ<-raw b c -> (a + b) < (a + c)}
      (\_ _ _ -> isPropΠ (\_ -> isProp-< _ _))
      convert
      a b c b<c
    where
    convert : (a b c : ℚ') -> b ℚ'< c -> ([ a ] + [ b ]) < ([ a ] + [ c ])
    convert a b c b<c = ℚ<-cons (subst2 ℚ<-raw (sym r+-eval) (sym r+-eval) (r+'₁-preserves-< a b c b<c))

  r*-preserves-0< : (a b : ℚ) -> 0r < a -> 0r < b -> 0r < (a * b)
  r*-preserves-0< a b (ℚ<-cons 0<a) (ℚ<-cons 0<b) =
    RationalElim.elimProp2
      {C2 = \a b -> ℚ<-raw 0r a -> ℚ<-raw 0r b -> 0r < (a * b)}
      (\_ _ -> isPropΠ2 (\_ _ -> isProp-< _ _))
      convert
      a b 0<a 0<b
    where
    convert : (a b  : ℚ') -> 0r' ℚ'< a -> 0r' ℚ'< b -> 0r < ([ a ] * [ b ])
    convert a b 0<a 0<b = ℚ<-cons (subst (ℚ<-raw 0r) (sym r*-eval) (r*'-preserves-0< a b 0<a 0<b))

instance
  LinearlyOrderedSemiringStr-ℚ : LinearlyOrderedSemiringStr RationalSemiring LinearOrderStr-ℚ
  LinearlyOrderedSemiringStr-ℚ = record
    { +₁-preserves-< = r+₁-preserves-<
    ; *-preserves-0< = r*-preserves-0<
    }
