{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order2 where

open import abs
open import base
open import equality
open import fraction.sign
open import fraction.order
open import functions
open import hlevel
open import isomorphism
open import order
open import order.instances.int
open import ordered-semiring
open import ordered-ring
open import rational
open import rational.difference
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

import int as i
import nat
open nat using (ℕ ; Nat⁺; 2⁺ ; _*⁺_)

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

module _ where
  private
    module M where
      abstract
        ℚ≤-elim : {ℓ : Level} {P : ℚ -> ℚ -> Type ℓ} ->
                  ({q r : ℚ} -> isProp (P q r)) ->
                  ({q r : ℚ} -> q ℚ< r -> P q r) ->
                  ({q r : ℚ} -> q == r -> P q r) ->
                  (q r : ℚ) -> q ℚ≤ r -> P q r
        ℚ≤-elim {P = P} isProp-P f< f= q r (ℚ≤-cons q≤r) =
          RationalElim.elimProp2
            {C2 = (\q r -> (ℚ≤-raw q r) -> P q r)}
            (\_ _ -> isPropΠ (\_ -> isProp-P))
            g≤ q r q≤r

          where
          g< : {q r : ℚ'} -> (q ℚ'< r) -> P [ q ] [ r ]
          g< = f< ∘ ℚ<-cons

          g= : {q r : ℚ'} -> (q r~ r) -> P [ q ] [ r ]
          g= = f= ∘ (eq/ _ _ )

          g≤ : (q r : ℚ') -> (ℚ≤-raw [ q ] [ r ]) -> P [ q ] [ r ]
          g≤ = ℚ'≤-elim g< g=

  open M public




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



  refl-ℚ≤ : Reflexive _ℚ≤_
  refl-ℚ≤ {a} =
    RationalElim.elimProp
      {C = (\r -> r ℚ≤ r)}
      (\_ -> isProp-ℚ≤)
      (\r -> (ℚ≤-cons (refl-ℚ'≤ {r}))) a

  trans-ℚ≤ : Transitive _ℚ≤_
  trans-ℚ≤ {a} {b} {c} (ℚ≤-cons a≤b) (ℚ≤-cons b≤c) =
    RationalElim.elimProp3
      {C3 = (\a b c -> ℚ≤-raw a b -> ℚ≤-raw b c -> a ℚ≤ c)}
      (\_ _ _ -> isPropΠ2 (\_ _ -> isProp-ℚ≤))
      (\a b c a≤b b≤c -> ℚ≤-cons (trans-ℚ'≤ a≤b b≤c))
      a b c a≤b b≤c

  antisym-ℚ≤ : Antisymmetric _ℚ≤_
  antisym-ℚ≤ {a} {b} (ℚ≤-cons a≤b) (ℚ≤-cons b≤a) =
    RationalElim.elimProp2
      {C2 = (\a b -> (ℚ≤-raw a b) -> (ℚ≤-raw b a) -> a == b)}
      (\_ _ -> isPropΠ2 (\_ _ -> isSetRational _ _))
      (\a b a≤b b≤a -> eq/ _ _ (antisym~-ℚ'≤ a≤b b≤a))
      a b a≤b b≤a

  connex-ℚ≤ : Connex _ℚ≤_
  connex-ℚ≤ =
    RationalElim.elimProp2
      {C2 = (\a b -> ∥ (a ℚ≤ b) ⊎ (b ℚ≤ a) ∥)}
      (\_ _ -> squash )
      (\a b -> ∥-map (⊎-map ℚ≤-cons ℚ≤-cons) (connex-ℚ'≤ a b))

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


  TotalOrderStr-ℚ : TotalOrderStr ℚ ℓ-zero
  TotalOrderStr-ℚ = record
    { _≤_ = _ℚ≤_
    ; isProp-≤ = \_ _ -> isProp-ℚ≤
    ; refl-≤ = refl-ℚ≤
    ; trans-≤ = \{a} {b} {c} -> trans-ℚ≤ {a} {b} {c}
    ; antisym-≤ = antisym-ℚ≤
    ; connex-≤ = connex-ℚ≤
    }

abstract
  trichotomous-ℚ< : Trichotomous _ℚ<_
  trichotomous-ℚ< a b =
    RationalElim.elimProp2
      {C2 = (\a b -> Triℚ< a b)}
      isProp-Triℚ<
      f a b

    where
    Triℚ< : Rel ℚ ℓ-zero
    Triℚ< x y = Tri (x ℚ< y) (x == y) (y ℚ< x)

    isProp-Triℚ< : (x y : ℚ) -> isProp (Triℚ< x y)
    isProp-Triℚ< x y = isProp-Tri isProp-ℚ< (isSetRational x y) isProp-ℚ<

    f : (a b : ℚ') -> Triℚ< [ a ] [ b ]
    f a b = handle (trichotomous~-ℚ'< a b)
      where
      handle : Tri (a ℚ'< b) (a r~ b) (b ℚ'< a) -> Triℚ< [ a ] [ b ]
      handle (tri< a<b' _ _) = tri< a<b (<->!= a<b) (asym-< a<b)
        where
        a<b = (ℚ<-cons a<b')
      handle (tri= _ a~b _) = tri= (=->≮ a=b) a=b (=->≮ (sym a=b))
        where
        a=b = (eq/ _ _ a~b)
      handle (tri> _ _ b<a') = tri> (asym-< b<a) (<->!= b<a ∘ sym) b<a
        where
        b<a = (ℚ<-cons b<a')

instance
  DecidableLinearOrderStr-ℚ : DecidableLinearOrderStr LinearOrderStr-ℚ
  DecidableLinearOrderStr-ℚ = record
    { trichotomous-< = trichotomous-ℚ<
    }


abstract
  weaken-ℚ< : {a b : ℚ} -> a ℚ< b -> a ℚ≤ b
  weaken-ℚ< {a} {b} (ℚ<-cons a<b) =
    RationalElim.elimProp2
      {C2 = (\a b -> (ℚ<-raw a b) -> (a ℚ≤ b))}
      (\_ _ -> isPropΠ (\_ -> isProp-ℚ≤))
      (\a b a<b -> (ℚ≤-cons (weaken-ℚ'< a<b)))
      a b a<b

  strengthen-ℚ≤-≠ : {a b : ℚ} -> a ℚ≤ b -> a != b -> a < b
  strengthen-ℚ≤-≠ =
    ℚ≤-elim {P = \a b -> a != b -> a < b }
            (isPropΠ (\_ -> isProp-< _ _))
            (\x _ -> x)
            (\a=b a!=b -> bot-elim (a!=b a=b)) _ _

instance
  CompatibleOrderStr-ℚ :
    CompatibleOrderStr ℚ ℓ-zero ℓ-zero LinearOrderStr-ℚ TotalOrderStr-ℚ
  CompatibleOrderStr-ℚ = record
    { weaken-< = weaken-ℚ<
    ; strengthen-≤-≠ = strengthen-ℚ≤-≠
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

private
  abstract
    decide-signℚ : (q : Rational) -> Σ[ s ∈ Sign ] (isSign s q)
    decide-signℚ q = handle (trichotomous-< q 0r)
      where
        handle : Tri (q ℚ< 0r) (q == 0r) (0r ℚ< q) -> Σ[ s ∈ Sign ] (isSign s q)
        handle (tri< q<0 _ _) = neg-sign , q<0
        handle (tri= _ q=0 _) = zero-sign , q=0
        handle (tri> _ _ 0<q) = pos-sign , 0<q

instance
  DecidableSignStr-ℚ : DecidableSignStr SignStr-ℚ
  DecidableSignStr-ℚ = record
    { decide-sign = decide-signℚ
    }


abstract
  Zero-0r : Zero 0r
  Zero-0r = refl

  same-sign-ℚ' : (s : Sign) (q : ℚ') -> isSign s q -> isSign s [ q ]
  same-sign-ℚ' pos-sign q pos-q = (ℚ<-cons 0<'q)
    where
    pos-diff : Pos (q r+' 0r')
    pos-diff = subst Pos (sym (r+'-right-zero q)) pos-q

    0<'q : 0r' ℚ'< q
    0<'q = (ℚ'<-cons pos-diff)
  same-sign-ℚ' neg-sign q neg-q = (ℚ<-cons q<'0)
    where
    pos-diff : Pos (0r' r+' (r-' q))
    pos-diff = subst Pos (sym (r+'-left-zero (r-' q))) (r-'-flips-sign q neg-sign neg-q)

    q<'0 : q ℚ'< 0r'
    q<'0 = (ℚ'<-cons pos-diff)
  same-sign-ℚ' zero-sign q zq = (eq/ _ _ q~0r)
    where
    q~0r : q r~ 0r'
    q~0r = Zero-r~ zq

  NonNeg-ℚ'->ℚ : {q : Rational'} -> NonNeg q -> NonNeg [ q ]
  NonNeg-ℚ'->ℚ (inj-l p) = inj-l (same-sign-ℚ' _ _ p)
  NonNeg-ℚ'->ℚ (inj-r p) = inj-r (same-sign-ℚ' _ _ p)

  same-sign-ℚ'⁻ : (s : Sign) (q : ℚ') -> isSign s [ q ] -> isSign s q
  same-sign-ℚ'⁻ s q' sq = subst (\x -> (isSign x q')) s2=s s2q'
    where
    Σs2q' = decide-sign q'
    s2 = (fst Σs2q')
    s2q' = (snd Σs2q')
    q : ℚ
    q = [ q' ]
    s2=s : s2 == s
    s2=s = isSign-unique q s2 s (same-sign-ℚ' s2 q' s2q') sq

  Pos->Inv : {q : ℚ} -> Pos q -> ℚInv q
  Pos->Inv p = NonZero->¬Zero (inj-l p)

  Neg->Inv : {q : ℚ} -> Neg q -> ℚInv q
  Neg->Inv p = NonZero->¬Zero (inj-r p)


  Pos-1r : Pos 1r
  Pos-1r = same-sign-ℚ' pos-sign 1r' (Pos-ℕ⁺->ℚ' (1 , tt))

  Pos-ℕ⁺->ℚ : (n : Nat⁺) -> Pos (ℕ->ℚ ⟨ n ⟩)
  Pos-ℕ⁺->ℚ n⁺@(n@(suc _), _) = same-sign-ℚ' pos-sign _ (Pos-ℕ⁺->ℚ' n⁺)

  1/ℕ-inv-path : (n : Nat⁺) -> 1/ℕ n == (r1/ (ℕ->ℚ ⟨ n ⟩) (Pos->Inv (Pos-ℕ⁺->ℚ n)))
  1/ℕ-inv-path n =
    sym *-left-one >=>
    *-left (sym (r1/-inverse n' i)) >=>
    *-assoc >=>
    *-right (*-commute >=> 1/ℕ-ℕ-path n) >=>
    *-right-one
    where
    n' = (ℕ->ℚ ⟨ n ⟩)
    i = (Pos->Inv (Pos-ℕ⁺->ℚ n))



ℚ⁺ : Type₀
ℚ⁺ = Σ ℚ Pos
ℚ⁻ : Type₀
ℚ⁻ = Σ ℚ Neg

ℚ⁰⁺ : Type₀
ℚ⁰⁺ = Σ ℚ NonNeg
ℚ⁰⁻ : Type₀
ℚ⁰⁻ = Σ ℚ NonPos


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


module _ where
  private
    module M where
      abstract
        r+₁-preserves-≤ : (a b c : ℚ) -> b ≤ c -> (a + b) ≤ (a + c)
        r+₁-preserves-≤ a = ℚ≤-elim (isProp-≤ _ _) f< f=
          where
          f< : {b c : ℚ} -> b < c -> _
          f< = weaken-< ∘ r+₁-preserves-< a _ _

          f= : {b c : ℚ} -> b == c -> _
          f= = =->≤ ∘ (cong (a +_))
  open M public


private
  module _ where
    private
      module M where
        abstract
          ℚ0≤-elim : {ℓ : Level} {P : ℚ -> Type ℓ} ->
                     ({q : ℚ} -> isProp (P q)) ->
                     ({q : ℚ} -> 0r ℚ< q -> P q) ->
                     ({q : ℚ} -> 0r == q -> P q) ->
                     (q : ℚ) -> 0r ℚ≤ q -> P q
          ℚ0≤-elim {P = P} isProp-P f< f= r 0≤r =
            ℚ≤-elim {P = \ z q -> z == 0r -> P q}
              (\{z} {q} -> (isPropΠ \_ -> isProp-P {q}))
              g< g=
              0r r 0≤r refl
            where
             g< : {z q : ℚ} -> z < q -> z == 0r -> P q
             g< {z} {q} z<q z=0 = f< (subst (_< q) z=0 z<q)

             g= : {z q : ℚ} -> z == q -> z == 0r -> P q
             g= {z} {q} z=q z=0 = f= (subst (_== q) z=0 z=q)
    open M public

abstract

  r*-preserves-0≤ : (a b : ℚ) -> 0r ≤ a -> 0r ≤ b -> 0r ≤ (a * b)
  r*-preserves-0≤ a b 0≤a 0≤b =
    ℚ0≤-elim {P = \a -> ∀ b -> 0r ≤ b -> 0r ≤ (a * b)}
      (isPropΠ2 (\_ _ -> (isProp-≤ _ _))) f< f= a 0≤a b 0≤b
    where
    f= : {a : ℚ} -> 0r == a -> (b : ℚ) -> 0r ≤ b -> 0r ≤ (a * b)
    f= 0=a _ _ = =->≤ (sym *-left-zero >=> *-left 0=a)

    f< : {a : ℚ} -> 0r < a -> (b : ℚ) -> 0r ≤ b -> 0r ≤ (a * b)
    f< {a} 0<a = ℚ0≤-elim (isProp-≤ _ _) g< g=
      where
      g< : {b : ℚ} -> 0r < b -> 0r ≤ (a * b)
      g< 0<b = weaken-< (*-preserves-0< _ _ 0<a 0<b)

      g= : {b : ℚ} -> 0r == b -> 0r ≤ (a * b)
      g= 0=b = =->≤ (sym *-right-zero >=> *-right 0=b)

instance
  TotallyOrderedSemiringStr-ℚ : TotallyOrderedSemiringStr RationalSemiring TotalOrderStr-ℚ
  TotallyOrderedSemiringStr-ℚ = record
    { +₁-preserves-≤ = r+₁-preserves-≤
    ; *-preserves-0≤ = r*-preserves-0≤
    }


-- Compatibility functions

Zero-path : (q : Rational) -> Zeroℚ q -> q == 0r
Zero-path _ p = p

r--flips-sign : (q : Rational) (s : Sign) -> (isSignℚ s q) -> (isSignℚ (s⁻¹ s) (r- q))
r--flips-sign q pos-sign 0<q = minus-flips-< _ _ 0<q
r--flips-sign q zero-sign q=0 = cong -_ q=0
r--flips-sign q neg-sign q<0 = minus-flips-< _ _ q<0

r--NonNeg : {q1 : ℚ} -> NonNeg q1 -> NonPos (r- q1)
r--NonNeg (inj-l s) = (inj-l (r--flips-sign _ pos-sign s))
r--NonNeg (inj-r s) = (inj-r (r--flips-sign _ zero-sign s))

r--NonPos : {q1 : ℚ} -> NonPos q1 -> NonNeg (r- q1)
r--NonPos (inj-l s) = (inj-l (r--flips-sign _ neg-sign s))
r--NonPos (inj-r s) = (inj-r (r--flips-sign _ zero-sign s))

NonNeg-0≤ : (q : Rational) -> NonNeg q -> 0r ≤ q
NonNeg-0≤ _ (inj-l pq) = weaken-ℚ< pq
NonNeg-0≤ q (inj-r zq) = subst (_≤ q) zq refl-≤

NonPos-≤0 : (q : Rational) -> NonPos q -> q ≤ 0r
NonPos-≤0 _ (inj-l nq) = weaken-ℚ< nq
NonPos-≤0 q (inj-r zq) = subst (q ≤_) zq refl-≤

0≤-NonNeg : (q : Rational) -> 0r ≤ q -> NonNeg q
0≤-NonNeg q 0≤q = ℚ0≤-elim (isProp-NonNeg _) inj-l (inj-r ∘ sym) q 0≤q

≤0-NonPos : (q : Rational) -> q ≤ 0r -> NonPos q
≤0-NonPos q q≤0 =
  subst NonPos minus-double-inverse (r--NonNeg (0≤-NonNeg (r- q) (minus-flips-≤ q 0r q≤0)))

Pos-0< : (q : Rational) -> Pos q -> 0r < q
Pos-0< q 0<q = 0<q

Neg-<0 : (q : Rational) -> Neg q -> q < 0r
Neg-<0 q q<0 = q<0

0<-Pos : (q : Rational) -> 0r < q -> Pos q
0<-Pos q 0<q = 0<q

<0-Neg : (q : Rational) -> q < 0r -> Neg q
<0-Neg q q<0 = q<0

NonPos≤NonNeg : {q r : Rational} -> NonPos q -> NonNeg r -> q ℚ≤ r
NonPos≤NonNeg np-q nn-r = trans-≤ (NonPos-≤0 _ np-q) (NonNeg-0≤ _ nn-r)

NonNeg-≤ : (a b : ℚ) -> NonNeg a -> a ℚ≤ b -> NonNeg b
NonNeg-≤ a b (inj-l 0<a) a≤b = 0≤-NonNeg _ (trans-≤ (weaken-< 0<a) a≤b)
NonNeg-≤ a b (inj-r za) a≤b = 0≤-NonNeg _ (trans-≤ (=->≤ (sym (Zero-path a za))) a≤b)

NonPos-≤ : (a b : ℚ) -> NonPos b -> a ℚ≤ b -> NonPos a
NonPos-≤ a b (inj-l b<0) a≤b = ≤0-NonPos _ (trans-≤ a≤b (weaken-< b<0))
NonPos-≤ a b (inj-r zb) a≤b = ≤0-NonPos _ (trans-≤ a≤b (=->≤ (Zero-path b zb)))

Pos-≤ : (a b : ℚ) -> Pos a -> a ℚ≤ b -> Pos b
Pos-≤ a b 0<a a≤b = trans-<-≤ 0<a a≤b

Neg-≤ : (a b : ℚ) -> Neg b -> a ℚ≤ b -> Neg a
Neg-≤ a b b<0 a≤b = trans-≤-< a≤b b<0

Pos-< : (a b : ℚ) -> NonNeg a -> a ℚ< b -> Pos b
Pos-< a b nn a<b = trans-≤-< (NonNeg-0≤ _ nn) a<b

Neg-< : (a b : ℚ) -> NonPos b -> a ℚ< b -> Neg a
Neg-< a b np a<b = trans-<-≤ a<b (NonPos-≤0 _ np)

r*₁-preserves-order : (a : ℚ⁺) (b c : ℚ) -> b ℚ< c -> (⟨ a ⟩ r* b) ℚ< (⟨ a ⟩ r* c)
r*₁-preserves-order (a , 0<a) b c b<c = *₁-preserves-< a b c 0<a b<c

r*₂-preserves-order : (a b : ℚ) (c : ℚ⁺) -> a ℚ< b -> (a r* ⟨ c ⟩) ℚ< (b r* ⟨ c ⟩)
r*₂-preserves-order a b (c , 0<c) a<b = *₂-preserves-< a b c a<b 0<c

r*₁-flips-order : (a : ℚ⁻) (b c : ℚ) -> b ℚ< c -> (⟨ a ⟩ r* c) ℚ< (⟨ a ⟩ r* b)
r*₁-flips-order (a , a<0) b c b<c = *₁-flips-< a b c a<0 b<c

r*₂-flips-order : (a b : ℚ) (c : ℚ⁻) -> a ℚ< b -> (b r* ⟨ c ⟩) ℚ< (a r* ⟨ c ⟩)
r*₂-flips-order a b (c , c<0) a<b = *₂-flips-< a b c a<b c<0

r*₁-preserves-≤ : (a : ℚ⁰⁺) (b c : ℚ) -> b ℚ≤ c -> (⟨ a ⟩ r* b) ℚ≤ (⟨ a ⟩ r* c)
r*₁-preserves-≤ (a , (inj-l 0<a)) b c b≤c = *₁-preserves-≤ a b c (weaken-< 0<a) b≤c
r*₁-preserves-≤ (a , (inj-r za)) b c b≤c = *₁-preserves-≤ a b c (=->≤ (sym (Zero-path a za))) b≤c

r*₁-flips-≤ : (a : ℚ⁰⁻) (b c : ℚ) -> b ℚ≤ c -> (⟨ a ⟩ r* c) ℚ≤ (⟨ a ⟩ r* b)
r*₁-flips-≤ (a , (inj-l a<0)) b c b≤c = *₁-flips-≤ a b c (weaken-< a<0) b≤c
r*₁-flips-≤ (a , (inj-r za)) b c b≤c = *₁-flips-≤ a b c (=->≤ (Zero-path a za)) b≤c

r*₂-flips-≤ : (a b : ℚ) (c : ℚ⁰⁻) -> a ℚ≤ b -> (b r* ⟨ c ⟩) ℚ≤ (a r* ⟨ c ⟩)
r*₂-flips-≤ a b (c , (inj-l c<0)) a≤b = *₂-flips-≤ a b c a≤b (weaken-< c<0)
r*₂-flips-≤ a b (c , (inj-r zc)) a≤b = *₂-flips-≤ a b c a≤b (=->≤ (Zero-path c zc))

r*₂-preserves-≤ : (a b : ℚ) (c : ℚ⁰⁺) -> a ℚ≤ b -> (a r* ⟨ c ⟩) ℚ≤ (b r* ⟨ c ⟩)
r*₂-preserves-≤ a b (c , (inj-l 0<c)) a≤b = *₂-preserves-≤ a b c a≤b (weaken-< 0<c)
r*₂-preserves-≤ a b (c , (inj-r zc)) a≤b = *₂-preserves-≤ a b c a≤b (=->≤ (sym (Zero-path c zc)))

r*-Pos-Pos : {q1 q2 : ℚ} -> Pos q1 -> Pos q2 -> Pos (q1 r* q2)
r*-Pos-Pos p1 p2 = r*-preserves-0< _ _ p1 p2

r*-Pos-Neg : {q1 q2 : ℚ} -> Pos q1 -> Neg q2 -> Neg (q1 r* q2)
r*-Pos-Neg {q1} {q2} p1 n2 =
  subst ((q1 * q2) <_) *-right-zero (*₁-preserves-< q1 q2 0r p1 n2)

r*-Neg-Pos : {q1 q2 : ℚ} -> Neg q1 -> Pos q2 -> Neg (q1 r* q2)
r*-Neg-Pos n1 p2 = subst Neg *-commute (r*-Pos-Neg p2 n1)

r*-Neg-Neg : {q1 q2 : ℚ} -> Neg q1 -> Neg q2 -> Pos (q1 r* q2)
r*-Neg-Neg {q1} {q2} n1 n2 = subst (_< (q1 * q2)) *-right-zero (*₁-flips-< q1 q2 0r n1 n2)


r*-NonNeg-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r* q2)
r*-NonNeg-NonNeg nn1 nn2 = 0≤-NonNeg _ (r*-preserves-0≤ _ _ (NonNeg-0≤ _ nn1) (NonNeg-0≤ _ nn2))

r*-NonNeg-NonPos : {q1 q2 : ℚ} -> NonNeg q1 -> NonPos q2 -> NonPos (q1 r* q2)
r*-NonNeg-NonPos {q1} {q2} nn1 np2 = ≤0-NonPos _ q1q2≤0
  where
  q1q2≤0 : (q1 * q2) ≤ 0r
  q1q2≤0 = subst ((q1 * q2) ≤_) *-right-zero (*₁-preserves-≤ q1 q2 0r (NonNeg-0≤ _ nn1) (NonPos-≤0 _ np2))

r*-NonPos-NonNeg : {q1 q2 : ℚ} -> NonPos q1 -> NonNeg q2 -> NonPos (q1 r* q2)
r*-NonPos-NonNeg np nn = subst NonPos *-commute (r*-NonNeg-NonPos nn np)

r*-NonPos-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonNeg (q1 r* q2)
r*-NonPos-NonPos {q1} {q2} nn1 np2 = 0≤-NonNeg _ 0≤q1q2
  where
  0≤q1q2 : 0r ≤ (q1 * q2)
  0≤q1q2 = subst (_≤ (q1 * q2)) *-right-zero (*₁-flips-≤ q1 q2 0r (NonPos-≤0 _ nn1) (NonPos-≤0 _ np2))



r+-NonNeg-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r+ q2)
r+-NonNeg-NonNeg {q1} {q2} nn1 nn2 = 0≤-NonNeg (q1 + q2)
  (subst (_≤ (q1 + q2)) +-left-zero (+-preserves-≤ _ _ _ _ (NonNeg-0≤ q1 nn1) (NonNeg-0≤ q2 nn2)))

r+-NonPos-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonPos (q1 r+ q2)
r+-NonPos-NonPos {q1} {q2} np1 np2 = ≤0-NonPos (q1 + q2)
  (subst ((q1 + q2) ≤_) +-left-zero (+-preserves-≤ _ _ _ _ (NonPos-≤0 q1 np1) (NonPos-≤0 q2 np2)))


r*-preserves-Pos : (q1 q2 : Rational) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)
r*-preserves-Pos _ _ = r*-Pos-Pos


r+-preserves-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonPos (q1 r+ q2)
r+-preserves-NonPos = r+-NonPos-NonPos

r+-preserves-Pos : (q1 q2 : ℚ) -> Pos q1 -> Pos q2 -> Pos (q1 r+ q2)
r+-preserves-Pos q1 q2 p1 p2 =
  subst (_< (q1 + q2)) +-left-zero (+-preserves-< _ _ _ _ p1 p2)

r+-preserves-Neg : (q1 q2 : ℚ) -> Neg q1 -> Neg q2 -> Neg (q1 r+ q2)
r+-preserves-Neg q1 q2 p1 p2 =
  subst ((q1 + q2) <_) +-left-zero (+-preserves-< _ _ _ _ p1 p2)



r*-ZeroFactor : {q1 q2 : ℚ} -> Zero (q1 r* q2) -> Zero q1 ⊎ Zero q2
r*-ZeroFactor {q1} {q2} zp =
  handle (fst (decide-sign q1)) (fst (decide-sign q2)) (snd (decide-sign q1)) (snd (decide-sign q2))
  where
  handle : (s1 s2 : Sign) -> isSignℚ s1 q1 -> isSignℚ s2 q2 -> Zero q1 ⊎ Zero q2
  handle zero-sign _         z1 _ = inj-l z1
  handle pos-sign  zero-sign p1 z2 = inj-r z2
  handle neg-sign  zero-sign n1 z2 = inj-r z2
  handle pos-sign  pos-sign  p1 p2 =
    bot-elim (NonZero->¬Zero (inj-l (*-preserves-0< _ _ p1 p2)) zp)
  handle pos-sign  neg-sign  p1 n2 = bot-elim (NonZero->¬Zero (inj-r p<0) zp)
    where
    p<0 : (q1 * q2) < 0r
    p<0 = subst ((q1 * q2) <_) *-right-zero (*₁-preserves-< q1 q2 0r p1 n2)
  handle neg-sign  pos-sign  n1 p2 = bot-elim (NonZero->¬Zero (inj-r p<0) zp)
    where
    p<0 : (q1 * q2) < 0r
    p<0 = subst ((q1 * q2) <_) *-left-zero (*₂-preserves-< q1 0r q2 n1 p2)
  handle neg-sign  neg-sign  n1 n2 = bot-elim (NonZero->¬Zero (inj-l 0<p) zp)
    where
    0<p : 0r < (q1 * q2)
    0<p = subst (_< (q1 * q2)) *-right-zero (*₁-flips-< q1 q2 0r n1 n2)


r*₁-preserves-sign : (q : ℚ⁺) (r : Rational) {s : Sign} -> isSignℚ s r -> isSignℚ s (⟨ q ⟩ r* r)
r*₁-preserves-sign (q , pq) r {pos-sign} pr = r*-preserves-0< _ _ pq pr
r*₁-preserves-sign (q , pq) r {zero-sign} zr = *-right zr >=> *-right-zero
r*₁-preserves-sign (q , pq) r {neg-sign} nr = r*-Pos-Neg pq nr

r*₁-flips-sign : (q : ℚ⁻) (r : Rational) {s : Sign} -> isSignℚ s r -> isSignℚ (s⁻¹ s) (⟨ q ⟩ r* r)
r*₁-flips-sign (q , nq) r {pos-sign} pr = r*-Neg-Pos nq pr
r*₁-flips-sign (q , nq) r {zero-sign} zr = *-right zr >=> *-right-zero
r*₁-flips-sign (q , nq) r {neg-sign} nr = r*-Neg-Neg nq nr


r1/-preserves-Pos : (q : Rational) -> (i : ℚInv q) -> Pos q -> Pos (r1/ q i)
r1/-preserves-Pos q i pq = handle (decide-sign qi)
  where
  qi = (r1/ q i)
  handle : Σ[ s ∈ Sign ] (isSign s qi) -> Pos qi
  handle (pos-sign , pqi) = pqi
  handle (zero-sign , zqi) = bot-elim (NonPos->¬Pos (inj-r z1) Pos-1r)
    where
    z1 : Zero 1r
    z1 = subst Zero (*-commute >=> r1/-inverse q i) (r*₁-preserves-sign (q , pq) qi {zero-sign} zqi)
  handle (neg-sign , nqi) = bot-elim (NonPos->¬Pos (inj-l n1) Pos-1r)
    where
    n1 : Neg 1r
    n1 = subst Neg (*-commute >=> r1/-inverse q i) (r*₁-preserves-sign (q , pq) qi {neg-sign} nqi)



r1/-preserves-Neg : (q : Rational) -> (i : ℚInv q) -> Neg q -> Neg (r1/ q i)
r1/-preserves-Neg q i nq = handle (decide-sign qi)
  where
  qi = (r1/ q i)
  handle : Σ[ s ∈ Sign ] (isSign s qi) -> Neg qi
  handle (neg-sign , nqi) = nqi
  handle (zero-sign , zqi) = bot-elim (NonPos->¬Pos (inj-r z1) Pos-1r)
    where
    z1 : Zero 1r
    z1 = subst Zero (*-commute >=> r1/-inverse q i) (r*₁-flips-sign (q , nq) qi {zero-sign} zqi)
  handle (pos-sign , pqi) = bot-elim (NonPos->¬Pos (inj-l n1) Pos-1r)
    where
    n1 : Neg 1r
    n1 = subst Neg (*-commute >=> r1/-inverse q i) (r*₁-flips-sign (q , nq) qi {pos-sign} pqi)

Pos-1/ℕ : (n : Nat⁺) -> Pos (1/ℕ n)
Pos-1/ℕ n = subst Pos (sym (1/ℕ-inv-path n)) (r1/-preserves-Pos (ℕ->ℚ ⟨ n ⟩) _ (Pos-ℕ⁺->ℚ n))


--

1/2r<1r : 1/2r < 1r
1/2r<1r = subst2 _<_ (r+-left-zero 1/2r) (2r-path 1/2r >=> 2r-1/2r-path)  0r+1/2r<1/2r+1/2r
  where
  0<1/2r : 0r < 1/2r
  0<1/2r = (Pos-1/ℕ (2 , tt))

  0r+1/2r<1/2r+1/2r : (0r r+ 1/2r) < (1/2r r+ 1/2r)
  0r+1/2r<1/2r+1/2r = +₂-preserves-< 0r 1/2r 1/2r 0<1/2r

1/2ℕ<1/ℕ : (n : Nat⁺) -> 1/ℕ (2⁺ *⁺ n) < 1/ℕ n
1/2ℕ<1/ℕ n =
  subst2 _<_ (sym (1/2ℕ-path n)) (r*-left-one (1/ℕ n))
        (r*₂-preserves-order 1/2r 1r (1/ℕ n , Pos-1/ℕ n) 1/2r<1r)

NonNeg-diffℚ : (a b : ℚ) -> a ≤ b -> NonNeg (diffℚ a b)
NonNeg-diffℚ a b a≤b =
  0≤-NonNeg _ (subst (_≤ (diffℚ a b)) +-inverse (+₂-preserves-≤ a b (- a) a≤b))

NonNeg-diffℚ⁻ : (a b : ℚ) -> NonNeg (diffℚ a b) -> a ≤ b
NonNeg-diffℚ⁻ a b nn =
  subst2 _≤_ +-right-zero (diffℚ-step a b) (+₁-preserves-≤ a _ _ (NonNeg-0≤ _ nn))

Pos-diffℚ : (a b : ℚ) -> a < b -> Pos (diffℚ a b)
Pos-diffℚ a b a<b =
  subst (_< (diffℚ a b)) +-inverse (+₂-preserves-< a b (- a) a<b)

Pos-diffℚ⁻ : (a b : ℚ) -> Pos (diffℚ a b) -> a < b
Pos-diffℚ⁻ a b p =
  subst2 _<_ +-right-zero (diffℚ-step a b) (+₁-preserves-< a _ _ p)


dense-< : Dense _ℚ<_
dense-< {x} {y} lt = ∣ z , (Pos-diffℚ⁻ _ _ pos-d3 , Pos-diffℚ⁻ _ _ pos-d4) ∣
  where
  d1 = y r+ (r- x)
  d2 = d1 r* 1/2r
  z = x r+ d2
  z' = y r+ (r- d2)
  d3 = z r+ (r- x)
  d4 = y r+ (r- z)

  d2-path : d2 r+ d2 == d1
  d2-path = 1/2r-path d1

  z-path : z == z'
  z-path =
    begin
      x r+ d2
    ==< sym (r+-right-zero _) >
      (x r+ d2) r+ 0r
    ==< cong ((x r+ d2) r+_) (sym (r+-inverse d2)) >
      (x r+ d2) r+ (d2 r+ (r- d2))
    ==< r+-assoc x d2 (d2 r+ (r- d2)) >=>
        cong (x r+_) (sym (r+-assoc d2 d2 (r- d2)) >=> (cong (_r+ (r- d2)) d2-path)) >
      x r+ (d1 r+ (r- d2))
    ==< sym (r+-assoc x d1 (r- d2)) >
      (x r+ (y r+ (r- x))) r+ (r- d2)
    ==< cong (_r+ (r- d2)) (sym (r+-assoc x y (r- x)) >=>
                            cong (_r+ (r- x)) (r+-commute x y) >=>
                            r+-assoc y x (r- x) >=>
                            cong (y r+_) (r+-inverse x) >=>
                            r+-right-zero y) >
      y r+ (r- d2)
    end

  pos-d1 : Posℚ d1
  pos-d1 = Pos-diffℚ _ _ lt

  pos-d2 : Posℚ d2
  pos-d2 = r*-Pos-Pos pos-d1 (Pos-1/ℕ (2 , tt))

  d3-path : d2 == d3
  d3-path =
    sym (cong (_r+ (r- x)) (r+-commute x d2) >=>
         r+-assoc d2 x (r- x) >=>
         cong (d2 r+_) (r+-inverse x) >=>
         r+-right-zero d2)
  pos-d3 : Posℚ d3
  pos-d3 = subst Posℚ d3-path pos-d2

  d4-path : d2 == d4
  d4-path =
    sym (cong (\z -> y r+ (r- z)) z-path >=>
         cong (y r+_) minus-distrib-plus >=>
         sym (r+-assoc y (r- y) (r- (r- d2))) >=>
         cong2 _r+_ (r+-inverse y) minus-double-inverse >=>
         r+-left-zero d2)
  pos-d4 : Posℚ d4
  pos-d4 = subst Posℚ d4-path pos-d2

r+-Pos->order : (a : ℚ) (b : Σ ℚ Posℚ) -> a < (a r+ ⟨ b ⟩)
r+-Pos->order a (b , pos-b) =
  subst (_< (a + b)) +-right-zero (+₁-preserves-< a 0r b pos-b)

r+-Neg->order : (a : ℚ) (b : Σ ℚ Negℚ) -> a > (a r+ ⟨ b ⟩)
r+-Neg->order a (b , neg-b) =
  subst (_> (a + b)) +-right-zero (+₁-preserves-< a b 0r neg-b)


abstract
  ℕ->ℚ-preserves-order : (a b : Nat) -> a nat.< b -> (ℕ->ℚ a) < (ℕ->ℚ b)
  ℕ->ℚ-preserves-order a b a<b = ℚ<-cons (ℕ->ℚ'-preserves-order a b a<b)

1/ℕ-flips-order : (a b : Nat⁺) -> ⟨ a ⟩ nat.< ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
1/ℕ-flips-order a@(a' , _) b@(b' , _) lt = subst2 _<_ b-path a-path ab*<
  where
  ab = 1/ℕ a r* 1/ℕ b
  pos-ab : Pos ab
  pos-ab = r*-preserves-Pos _ _ (Pos-1/ℕ a) (Pos-1/ℕ b)

  a-path : (ab r* (ℕ->ℚ b')) == 1/ℕ a
  a-path =
    r*-assoc (1/ℕ a) (1/ℕ b) (ℕ->ℚ b') >=>
    cong (1/ℕ a r*_) (1/ℕ-ℕ-path b) >=>
    r*-right-one (1/ℕ a)
  b-path : (ab r* (ℕ->ℚ a')) == 1/ℕ b
  b-path =
    cong (_r* ℕ->ℚ a') (r*-commute (1/ℕ a) (1/ℕ b)) >=>
    r*-assoc (1/ℕ b) (1/ℕ a) (ℕ->ℚ a') >=>
    cong (1/ℕ b r*_) (1/ℕ-ℕ-path a) >=>
    r*-right-one (1/ℕ b)

  ab*< : (ab r* (ℕ->ℚ a')) < (ab r* (ℕ->ℚ b'))
  ab*< = r*₁-preserves-order (ab , pos-ab) (ℕ->ℚ a') (ℕ->ℚ b')
           (ℕ->ℚ-preserves-order a' b' lt)


private
  zero-diff->path : (x y : Rational) -> Zeroℚ (y r+ (r- x)) -> x == y
  zero-diff->path x y zyx = sym p
    where
    p : y == x
    p = sym (r+-right-zero y) >=>
        (cong (y r+_) (sym (r+-inverse x) >=> r+-commute x (r- x))) >=>
        sym (r+-assoc y (r- x) x) >=>
        cong (_r+ x) (Zero-path (y r+ (r- x)) zyx) >=>
        r+-left-zero x

r1/-Pos-flips-order : (a b : ℚ⁺) -> ⟨ a ⟩ < ⟨ b ⟩ ->
                      (r1/ ⟨ b ⟩ (Pos->Inv (snd b))) < (r1/ ⟨ a ⟩ (Pos->Inv (snd a)))
r1/-Pos-flips-order (a , pos-a) (b , pos-b) a<b =
  Pos-diffℚ⁻ b' a' (subst Pos path pos-prod)
  where
  inv-a = (Pos->Inv pos-a)
  inv-b = (Pos->Inv pos-b)
  a' = r1/ a inv-a
  b' = r1/ b inv-b
  pos-a' = r1/-preserves-Pos a inv-a pos-a
  pos-b' = r1/-preserves-Pos b inv-b pos-b

  pos-a'b' : Pos (a' r* b')
  pos-a'b' = r*₁-preserves-sign (_ , pos-a') b' {pos-sign} pos-b'

  pos-prod : Pos ((a' r* b') r* (b r+ (r- a)))
  pos-prod = r*₁-preserves-sign ((a' r* b') , pos-a'b') (b r+ (r- a)) {pos-sign} (Pos-diffℚ a b a<b)

  path : (a' r* b') r* (b r+ (r- a)) == a' r+ (r- b')
  path =
    *-distrib-+-left >=>
    +-cong (*-assoc >=> *-right (r1/-inverse b inv-b) >=> *-right-one)
           (r*-minus-extract-right _ _ >=>
            cong r-_ (*-left *-commute >=> *-assoc >=>
                      *-right (r1/-inverse a inv-a) >=> *-right-one))

r1/-Pos-flips-≤ : (a b : ℚ⁺) -> ⟨ a ⟩ ℚ≤ ⟨ b ⟩ ->
                  (r1/ ⟨ b ⟩ (Pos->Inv (snd b))) ℚ≤ (r1/ ⟨ a ⟩ (Pos->Inv (snd a)))
r1/-Pos-flips-≤ a@(a' , pos-a') b@(b' , pos-b') a≤b = handle (NonNeg-diffℚ a' b' a≤b)
  where
  handle : NonNeg (diffℚ a' b') -> _
  handle (inj-l pd) = weaken-< (r1/-Pos-flips-order a b (Pos-diffℚ⁻ a' b' pd))
  handle (inj-r zd) = =->≤ (sym path)
    where
    a==b = zero-diff->path a' b' zd

    path : (r1/ a' (Pos->Inv pos-a')) == (r1/ b' (Pos->Inv pos-b'))
    path i = (r1/ (a==b i) (Pos->Inv (isProp->PathP (\ j -> isProp-Pos (a==b j)) pos-a' pos-b' i)))



-- Archimedean


private
  open i using (int)

  nd⁺->ℚ' : (n : Nat) (d : Nat⁺) -> ℚ'
  nd⁺->ℚ' n (d , pos-d) = record
    { numerator = i.ℕ->ℤ n
    ; denominator = i.ℕ->ℤ d
    ; NonZero-denominator = i.Pos->NonZero (i.Pos'->Pos pos-d)
    }

  n⁺d⁺->ℚ' : (n d : Nat⁺) -> ℚ'
  n⁺d⁺->ℚ' (n' , _)  d = nd⁺->ℚ' n' d

  n⁺d⁺->ℚ : (n d : Nat⁺) -> ℚ
  n⁺d⁺->ℚ n d = [ n⁺d⁺->ℚ' n d ]

  n⁺d⁺->ℚ⁺ : (n d : Nat⁺) -> ℚ⁺
  n⁺d⁺->ℚ⁺ n d = n⁺d⁺->ℚ n d ,
           same-sign-ℚ' pos-sign _ (is-signℚ' (i.*-Pos-Pos (i.Pos'->Pos (snd n)) (i.Pos'->Pos (snd d))))


  ℚ⁺-elimProp :
    {ℓ : Level} -> {P : Pred ℚ⁺ ℓ} -> ((q : ℚ⁺) -> isProp (P q)) ->
    ((n d : Nat⁺) -> P (n⁺d⁺->ℚ⁺ n d)) ->
    (q : ℚ⁺) -> P q
  ℚ⁺-elimProp {P = P} isProp-P f (q , pos-q) =
    RationalElim.elimProp (\q -> isPropΠ (\pos-q -> isProp-P (q , pos-q))) handle q pos-q
    where
    find-rep : (q' : ℚ') -> (Pos q') -> Σ[ n ∈ Nat⁺ ] (Σ[ d ∈ Nat⁺ ] (n⁺d⁺->ℚ' n d r~ q'))
    find-rep (record { numerator = (i.pos n') ; denominator = (i.pos d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , refl)
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg _) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.pos _) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg n') ; denominator = (i.neg d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , i.minus-extract-right >=> sym i.minus-extract-left )
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-l ()})
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-r ()})

    handle : (q' : ℚ') -> (pos-q : (Pos [ q' ])) -> P ([ q' ] , pos-q)
    handle q' pos-q' = subst P path (f n d)
      where
      rep = find-rep q' (same-sign-ℚ'⁻ _ _ pos-q')
      n = fst rep
      d = fst (snd rep)
      nd~ = snd (snd rep)

      path : (n⁺d⁺->ℚ⁺ n d) == ([ q' ] , pos-q')
      path = ΣProp-path (\{x} -> isProp-Pos x) (eq/ _ _ nd~)


  1/ℕ-<-step1 : (n d : Nat⁺) -> (1/ℕ' d) ℚ'≤ (n⁺d⁺->ℚ' n d)
  1/ℕ-<-step1 n@(n'@(suc n'') , _)  d@(d' , pos-d) = ℚ'≤-cons ans
    where
    x1 = same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d))
    x2 = ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))

    NonNeg-numer : i.NonNeg (int n' i.+ (i.- (int 1)))
    NonNeg-numer = subst i.NonNeg (sym i.+-eval >=> i.+-commute) (i.NonNeg-nonneg n'')

    ans2 : NonNeg (same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)))
    ans2 = NonNeg-nd->ℚ' (i.*-NonNeg-NonNeg NonNeg-numer (i.Pos->NonNeg (i.Pos'->Pos pos-d)))

    ans~ : same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) r~ ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans~ = same-denom-r+'-r~ (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) refl

    ans : NonNeg ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans = r~-preserves-NonNeg {x1} {x2} ans2 ans~


  1/ℕ-<-step2 : (n d : Nat⁺) -> ∃[ m ∈ Nat⁺ ] ( 1/ℕ' m ℚ'≤ (n⁺d⁺->ℚ' n d))
  1/ℕ-<-step2 n d = ∣ d , 1/ℕ-<-step1 n d ∣

  abstract
    1/ℕ-<-step3 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩)
    1/ℕ-<-step3 = ℚ⁺-elimProp (\q -> squash) (\n d -> (∥-map (handle n d) (1/ℕ-<-step2 n d)))
      where
      handle : (n d : Nat⁺) -> Σ[ m ∈ Nat⁺ ] (1/ℕ' m ℚ'≤ (n⁺d⁺->ℚ' n d)) ->
               Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ (n⁺d⁺->ℚ n d))
      handle n d (m , p) = m , (ℚ≤-cons p)

small-1/ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
small-1/ℕ q = ∥-map handle (1/ℕ-<-step3 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩) -> Σ[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
  handle (m , m≤) = (2⁺ *⁺ m) , trans-<-≤ {d1 = 1/ℕ (2⁺ *⁺ m)} {1/ℕ m} {⟨ q ⟩} (1/2ℕ<1/ℕ m) m≤

private
  small-1/2^ℕ-step1 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < ⟨ q ⟩)
  small-1/2^ℕ-step1 q@(q' , _) = ∥-map handle (small-1/ℕ q)
    where
    handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m < q') -> Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q')
    handle (m@(m' , _) , lt) =
      m , trans-< {_} {_} {_} {1/ℕ (2⁺ nat.^⁺ m')} {1/ℕ m} {q'}
            (1/ℕ-flips-order m (2⁺ nat.^⁺ m') (nat.2^n-large m')) lt

small-1/2^ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < ⟨ q ⟩)
small-1/2^ℕ q@(q' , _) = ∥-map handle (small-1/2^ℕ-step1 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q') ->
           Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q')
  handle ((m , _) , lt) = m , subst (_< q') (1/2^ℕ-path m) lt


ℚ-archimedian : (q1 q2 : ℚ⁺) -> ∃[ n ∈ Nat ] (((1/2r r^ℕ⁰ n) r* ⟨ q1 ⟩) < ⟨ q2 ⟩)
ℚ-archimedian q1@(q1' , pos-q1) q2@(q2' , pos-q2) = ∥-map handle (small-1/2^ℕ q3)
  where
  iq1 : ℚInv q1'
  iq1 p = (NonZero->¬Zero (Pos->NonZero pos-q1) (subst Zero (sym p) Zero-0r))

  q3' = q2' r* (r1/ q1' iq1)
  q3 : ℚ⁺
  q3 = q3' , r*-preserves-Pos _ _ pos-q2 (r1/-preserves-Pos q1' iq1 pos-q1)

  q3-path : q3' r* q1' == q2'
  q3-path = r*-assoc q2' (r1/ q1' iq1) q1' >=>
            cong (q2' r*_) (r1/-inverse q1' iq1) >=>
            r*-right-one q2'

  handle : Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q3') ->
           Σ[ m ∈ Nat ] (((1/2r r^ℕ⁰ m) r* q1') < q2')
  handle (m , lt) = m , subst (((1/2r r^ℕ⁰ m) r* q1') <_) q3-path lt2
    where
    lt2 : ((1/2r r^ℕ⁰ m) r* q1') < (q3' r* q1')
    lt2 = r*₂-preserves-order (1/2r r^ℕ⁰ m) q3' q1 lt

seperate-< : (a b : ℚ) -> a < b -> Σ[ ε ∈ ℚ⁺ ] (a r+ ⟨ ε ⟩) < (b r+ (r- ⟨ ε ⟩))
seperate-< a b a<b = ε , Pos-diffℚ⁻ (a r+ ε') (b r+ (r- ε')) pos-diff
  where
  Pos-1/2r = Pos-1/ℕ 2⁺
  ε' = 1/2r r* (1/2r r* (diffℚ a b))
  ε : ℚ⁺
  ε = ε' , r*-preserves-Pos 1/2r _ Pos-1/2r
                            (r*-preserves-Pos 1/2r (diffℚ a b) Pos-1/2r (Pos-diffℚ a b a<b))

  path : (diffℚ (a r+ ε') (b r+ (r- ε'))) == 1/2r r* (diffℚ a b)
  path =
    sym (r+-swap-diffℚ a b ε' (r- ε')) >=>
    cong2 _r+_
          (sym (r*-left-one (diffℚ a b)))
          (sym minus-distrib-plus >=>
           cong r-_ (1/2r-path' (1/2r r* (diffℚ a b))) >=>
           sym minus-extract-left) >=>
    sym (*-distrib-+-right {_} {_} {1r} {r- 1/2r} {diffℚ a b}) >=>
    cong (_r* (diffℚ a b)) (cong (_r+ (r- 1/2r)) (sym (1/2r-path 1r) >=>
                                                  cong2 _+_ (r*-left-one 1/2r) (r*-left-one 1/2r)) >=>
                            r+-assoc 1/2r 1/2r (r- 1/2r) >=>
                            diffℚ-step 1/2r 1/2r)

  pos-diff : Pos (diffℚ (a r+ ε') (b r+ (r- ε')))
  pos-diff = subst Pos (sym path) (r*-preserves-Pos 1/2r (diffℚ a b) (Pos-1/ℕ 2⁺) (Pos-diffℚ a b a<b))
