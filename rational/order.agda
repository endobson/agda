{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import apartness
open import additive-group
open import additive-group.instances.int
open import base
open import equality
open import equivalence
open import fraction.sign
open import fraction.order
open import functions
open import hlevel
open import hlevel.htype
open import int.addition
open import int.order
open import isomorphism
open import nat using (ℕ ; Nat⁺; 1⁺ ; 2⁺ ; _*⁺_)
open import nat.exponentiation
open import nat.order using (2^n-large)
open import order
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.decidable
open import ordered-semiring
open import ordered-semiring.instances.int
open import ordered-semiring.ring
open import ordered-semiring.decidable
open import ordered-ring
open import rational
open import relation
open import ring
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.exponentiation
open import set-quotient
open import sigma.base
open import sign
open import sign.instances.fraction
open import sum
open import truncation
open import univalence

import int as i
open EqReasoning

module _ where
  module _ where
    private
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

      opaque
        unfolding ℚ
        ℚ<-full : ℚ -> ℚ -> hProp ℓ-zero
        ℚ<-full = SetQuotientElim.rec2 isSet-hProp val preserved₁ preserved₂

    opaque
      unfolding ℚ<-full

      ℚ<-raw : Rel ℚ ℓ-zero
      ℚ<-raw q r = ⟨ ℚ<-full q r ⟩

      isProp-ℚ<-raw : (q r : ℚ) -> isProp (ℚ<-raw q r)
      isProp-ℚ<-raw q r = snd (ℚ<-full q r)

      ℚ<-raw-eval : {q r : ℚ'} -> ℚ<-raw (ℚ'->ℚ q) (ℚ'->ℚ r) == q ℚ'< r
      ℚ<-raw-eval {q} {r} = refl

  module _ where
    private
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

      opaque
        unfolding ℚ
        ℚ≤-full : ℚ -> ℚ -> hProp ℓ-zero
        ℚ≤-full = SetQuotientElim.rec2 isSet-hProp val preserved₁ preserved₂

    opaque
      unfolding ℚ≤-full

      ℚ≤-raw : ℚ -> ℚ -> Type₀
      ℚ≤-raw q r = ⟨ ℚ≤-full q r ⟩

      isProp-ℚ≤-raw : (q r : ℚ) -> isProp (ℚ≤-raw q r)
      isProp-ℚ≤-raw q r = snd (ℚ≤-full q r)

      ℚ≤-raw-eval : {q r : ℚ'} -> ℚ≤-raw (ℚ'->ℚ q) (ℚ'->ℚ r) == q ℚ'≤ r
      ℚ≤-raw-eval {q} {r} = refl


record _ℚ<_ (q : ℚ) (r : ℚ) : Type₀ where
  no-eta-equality ; pattern
  constructor ℚ<-cons
  field
    v : ℚ<-raw q r

record _ℚ≤_ (q : ℚ) (r : ℚ) : Type₀ where
  no-eta-equality ; pattern
  constructor ℚ≤-cons
  field
    v : ℚ≤-raw q r

module _ where
  private
    module M where
      opaque
        unfolding ℚ

        ℚ≤-elim : {ℓ : Level} {P : ℚ -> ℚ -> Type ℓ} ->
                  ({q r : ℚ} -> isProp (P q r)) ->
                  ({q r : ℚ} -> q ℚ< r -> P q r) ->
                  ({q r : ℚ} -> q == r -> P q r) ->
                  (q r : ℚ) -> q ℚ≤ r -> P q r
        ℚ≤-elim {P = P} isProp-P f< f= q r (ℚ≤-cons q≤r) =
          SetQuotientElim.elimProp2
            {C2 = (\q r -> (ℚ≤-raw q r) -> P q r)}
            (\_ _ -> isPropΠ (\_ -> isProp-P))
            g≤ q r q≤r

          where
          g< : {q r : ℚ'} -> (q ℚ'< r) -> P (ℚ'->ℚ q) (ℚ'->ℚ r)
          g< = f< ∘ ℚ<-cons ∘ transport (sym ℚ<-raw-eval)

          g= : {q r : ℚ'} -> (q r~ r) -> P (ℚ'->ℚ q) (ℚ'->ℚ r)
          g= = f= ∘ (r~->path _ _)

          g≤ : (q r : ℚ') -> (ℚ≤-raw (ℚ'->ℚ q) (ℚ'->ℚ r)) -> P (ℚ'->ℚ q) (ℚ'->ℚ r)
          g≤ q r q≤r = ℚ'≤-elim g< g= q r (transport ℚ≤-raw-eval q≤r)
  open M public




opaque
  unfolding ℚ

  isProp-ℚ< : {a b : ℚ} -> isProp (a ℚ< b)
  isProp-ℚ< {a} {b} (ℚ<-cons a<b1) (ℚ<-cons a<b2) =
    cong ℚ<-cons (isProp-ℚ<-raw a b a<b1 a<b2)

  isProp-ℚ≤ : {a b : ℚ} -> isProp (a ℚ≤ b)
  isProp-ℚ≤ {a} {b} (ℚ≤-cons a≤b1) (ℚ≤-cons a≤b2) =
    cong ℚ≤-cons (isProp-ℚ≤-raw a b a≤b1 a≤b2)


  irrefl-ℚ< : Irreflexive _ℚ<_
  irrefl-ℚ< {a} (ℚ<-cons a<a) =
    SetQuotientElim.elimProp
      {C = (\r -> ℚ<-raw r r -> Bot)}
      (\_ -> isPropΠ (\_ -> isPropBot))
      (\r r<r -> (irrefl-ℚ'< (transport ℚ<-raw-eval r<r))) a a<a


  trans-ℚ< : Transitive _ℚ<_
  trans-ℚ< {a} {b} {c} (ℚ<-cons a<b) (ℚ<-cons b<c) =
    SetQuotientElim.elimProp3
      {C3 = (\a b c -> ℚ<-raw a b -> ℚ<-raw b c -> a ℚ< c)}
      (\_ _ _ -> isPropΠ2 (\_ _ -> isProp-ℚ<))
      (\a b c a<b b<c -> ℚ<-cons
        (transport (sym ℚ<-raw-eval) (trans-ℚ'< (transport ℚ<-raw-eval a<b)
                                                (transport ℚ<-raw-eval b<c))))
      a b c a<b b<c

  asym-ℚ< : Asymmetric _ℚ<_
  asym-ℚ< lt1 lt2 = irrefl-ℚ< (trans-ℚ< lt1 lt2)

  connected-ℚ< : Connected _ℚ<_
  connected-ℚ< {a} {b} ¬a<b ¬b<a =
    SetQuotientElim.elimProp2
      {C2 = (\a b -> ¬ (ℚ<-raw a b) -> ¬ (ℚ<-raw b a) -> a == b)}
      (\_ _ -> isPropΠ2 (\_ _ -> isSetℚ _ _))
      (\a b ¬a<b ¬b<a ->
        r~->path _ _ (connected~-ℚ'< (¬a<b ∘ (transport (sym ℚ<-raw-eval)))
                                     (¬b<a ∘ (transport (sym ℚ<-raw-eval)))))
      a b (\a<b -> ¬a<b (ℚ<-cons a<b)) (\b<a -> ¬b<a (ℚ<-cons b<a))

  comparison-ℚ< : Comparison _ℚ<_
  comparison-ℚ< a b c (ℚ<-cons a<c) =
    SetQuotientElim.elimProp3
      {C3 = (\a b c -> ℚ<-raw a c -> ∥ (a ℚ< b) ⊎ (b ℚ< c) ∥)}
      (\_ _ _ -> isPropΠ (\_ -> squash))
      compare
      a b c a<c
    where
    compare : (a b c : ℚ') -> ℚ<-raw (ℚ'->ℚ a) (ℚ'->ℚ c) ->
              ∥ ((ℚ'->ℚ a) ℚ< (ℚ'->ℚ b)) ⊎ ((ℚ'->ℚ b) ℚ< (ℚ'->ℚ c)) ∥
    compare a b c a<c =
      ∥-map (⊎-map ℚ<-cons ℚ<-cons)
        (transport path (comparison-ℚ'< a b c (transport ℚ<-raw-eval a<c)))
      where
      module _ where
        path = cong ∥_∥ (cong2 _⊎_ (sym ℚ<-raw-eval) (sym ℚ<-raw-eval))


  refl-ℚ≤ : Reflexive _ℚ≤_
  refl-ℚ≤ {a} =
    SetQuotientElim.elimProp
      {C = (\r -> r ℚ≤ r)}
      (\_ -> isProp-ℚ≤)
      (\r -> (ℚ≤-cons (transport (sym ℚ≤-raw-eval) (refl-ℚ'≤ {r})))) a

  trans-ℚ≤ : Transitive _ℚ≤_
  trans-ℚ≤ {a} {b} {c} (ℚ≤-cons a≤b) (ℚ≤-cons b≤c) =
    SetQuotientElim.elimProp3
      {C3 = (\a b c -> ℚ≤-raw a b -> ℚ≤-raw b c -> a ℚ≤ c)}
      (\_ _ _ -> isPropΠ2 (\_ _ -> isProp-ℚ≤))
      (\a b c a≤b b≤c ->
        ℚ≤-cons (transport (sym ℚ≤-raw-eval) (trans-ℚ'≤ (transport ℚ≤-raw-eval a≤b)
                                                        (transport ℚ≤-raw-eval b≤c))))
      a b c a≤b b≤c

  antisym-ℚ≤ : Antisymmetric _ℚ≤_
  antisym-ℚ≤ {a} {b} (ℚ≤-cons a≤b) (ℚ≤-cons b≤a) =
    SetQuotientElim.elimProp2
      {C2 = (\a b -> (ℚ≤-raw a b) -> (ℚ≤-raw b a) -> a == b)}
      (\_ _ -> isPropΠ2 (\_ _ -> isSetℚ _ _))
      (\a b a≤b b≤a -> r~->path _ _ (antisym~-ℚ'≤ (transport ℚ≤-raw-eval a≤b)
                                                  (transport ℚ≤-raw-eval b≤a)))
      a b a≤b b≤a

  connex-ℚ≤ : Connex _ℚ≤_
  connex-ℚ≤ =
    SetQuotientElim.elimProp2
      {C2 = (\a b -> ∥ (a ℚ≤ b) ⊎ (b ℚ≤ a) ∥)}
      (\_ _ -> squash )
      (\a b -> ∥-map (⊎-map ℚ≤-cons ℚ≤-cons) (transport (sym path) (connex-ℚ'≤ a b)))
    where
    path : {a b : ℚ'} -> ∥ (ℚ≤-raw (ℚ'->ℚ a) (ℚ'->ℚ b)) ⊎ (ℚ≤-raw (ℚ'->ℚ b) (ℚ'->ℚ a)) ∥ ==
                         ∥ (a ℚ'≤ b) ⊎ (b ℚ'≤ a) ∥
    path = (cong ∥_∥ (cong2 _⊎_ ℚ≤-raw-eval ℚ≤-raw-eval))


instance
  isLinearOrder-ℚ< : isLinearOrder _ℚ<_
  isLinearOrder-ℚ< = record
    { isProp-< = isProp-ℚ<
    ; irrefl-< = irrefl-ℚ<
    ; trans-< = trans-ℚ<
    ; connected-< = connected-ℚ<
    ; comparison-< = comparison-ℚ<
    }

  isPartialOrder-ℚ≤ : isPartialOrder _ℚ≤_
  isPartialOrder-ℚ≤ = record
    { isProp-≤ = isProp-ℚ≤
    ; refl-≤ = refl-ℚ≤
    ; trans-≤ = \{a} {b} {c} -> trans-ℚ≤ {a} {b} {c}
    ; antisym-≤ = antisym-ℚ≤
    }

  TotalOrderStr-ℚ : TotalOrderStr useⁱ
  TotalOrderStr-ℚ = record
    { connex-≤ = connex-ℚ≤
    }

opaque
  unfolding ℚ

  trichotomous-ℚ< : Trichotomous _ℚ<_
  trichotomous-ℚ< a b =
    SetQuotientElim.elimProp2
      {C2 = (\a b -> Tri< a b)}
      (\_ _ -> isProp-Tri<)
      f a b

    where
    module _ where
      f : (a b : ℚ') -> Tri< (ℚ'->ℚ a) (ℚ'->ℚ b)
      f a b = handle (trichotomous~-ℚ'< a b)
        where
        handle : Tri (a ℚ'< b) (a r~ b) (b ℚ'< a) -> Tri< (ℚ'->ℚ a) (ℚ'->ℚ b)
        handle (tri< a<b' _ _) = tri<' a<b
          where
          a<b = (ℚ<-cons (transport (sym ℚ<-raw-eval) a<b'))
        handle (tri= _ a~b _) = tri=' a=b
          where
          a=b = (r~->path _ _ a~b)
        handle (tri> _ _ b<a') = tri>' b<a
          where
          b<a = (ℚ<-cons (transport (sym ℚ<-raw-eval) b<a'))

instance
  DecidableLinearOrderStr-ℚ : DecidableLinearOrderStr useⁱ
  DecidableLinearOrderStr-ℚ = record
    { trichotomous-< = trichotomous-ℚ<
    }


opaque
  unfolding ℚ

  weaken-ℚ< : {a b : ℚ} -> a ℚ< b -> a ℚ≤ b
  weaken-ℚ< {a} {b} (ℚ<-cons a<b) =
    SetQuotientElim.elimProp2
      {C2 = (\a b -> (ℚ<-raw a b) -> (a ℚ≤ b))}
      (\_ _ -> isPropΠ (\_ -> isProp-ℚ≤))
      (\a b a<b -> (ℚ≤-cons (transport (sym ℚ≤-raw-eval) (weaken-ℚ'< (transport ℚ<-raw-eval a<b)))))
      a b a<b

  convert-ℚ≮ : {a b : ℚ} -> ¬ (a ℚ< b) -> b ℚ≤ a
  convert-ℚ≮ {a} {b} a≮b = handle (trichotomous-< _ _)
    where
    handle : Tri< a b -> b ≤ a
    handle (tri< a<b _ _) = bot-elim (a≮b a<b)
    handle (tri= _ a=b _) = path-≤ (sym a=b)
    handle (tri> _ _ b<a) = weaken-ℚ< b<a


  strengthen-ℚ≤-≠ : {a b : ℚ} -> a ℚ≤ b -> a != b -> a < b
  strengthen-ℚ≤-≠ =
    ℚ≤-elim {P = \a b -> a != b -> a < b }
            (isPropΠ (\_ -> isProp-< {D = ℚ}))
            (\x _ -> x)
            (\a=b a!=b -> bot-elim (a!=b a=b)) _ _

instance
  CompatibleOrderStr-ℚ : CompatibleOrderStr useⁱ useⁱ
  CompatibleOrderStr-ℚ = record
    { convert-≮ = convert-ℚ≮
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
    isProp-isSignℚ pos-sign _ = isProp-<
    isProp-isSignℚ zero-sign _ = isSetℚ _ _
    isProp-isSignℚ neg-sign _ = isProp-<

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
    decide-signℚ : (q : ℚ) -> Σ[ s ∈ Sign ] (isSign s q)
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

  same-sign-ℚ' : (s : Sign) (q : ℚ') -> isSign s q -> isSign s (ℚ'->ℚ q )
  same-sign-ℚ' pos-sign q pos-q = (ℚ<-cons (transport (sym ℚ<-raw-eval) 0<'q))
    where
    pos-diff : Pos (q r+' 0r')
    pos-diff = subst Pos (sym (r+'-right-zero q)) pos-q

    0<'q : 0r' ℚ'< q
    0<'q = (ℚ'<-cons pos-diff)
  same-sign-ℚ' neg-sign q neg-q = (ℚ<-cons (transport (sym ℚ<-raw-eval) q<'0))
    where
    pos-diff : Pos (0r' r+' (r-' q))
    pos-diff = subst Pos (sym (r+'-left-zero (r-' q))) (r-'-flips-sign q neg-sign neg-q)

    q<'0 : q ℚ'< 0r'
    q<'0 = (ℚ'<-cons pos-diff)
  same-sign-ℚ' zero-sign q zq = (r~->path _ _ q~0r)
    where
    q~0r : q r~ 0r'
    q~0r = Zero-r~ zq

  NonNeg-ℚ'->ℚ : {q : ℚ'} -> NonNeg q -> NonNeg (ℚ'->ℚ q)
  NonNeg-ℚ'->ℚ (inj-l p) = inj-l (same-sign-ℚ' _ _ p)
  NonNeg-ℚ'->ℚ (inj-r p) = inj-r (same-sign-ℚ' _ _ p)

  same-sign-ℚ'⁻ : (s : Sign) (q : ℚ') -> isSign s (ℚ'->ℚ q) -> isSign s q
  same-sign-ℚ'⁻ s q' sq = subst (\x -> (isSign x q')) s2=s s2q'
    where
    module _ where
      Σs2q' = decide-sign q'
      s2 = (fst Σs2q')
      s2q' = (snd Σs2q')
      q : ℚ
      q = (ℚ'->ℚ q')
      s2=s : s2 == s
      s2=s = isSign-unique q s2 s (same-sign-ℚ' s2 q' s2q') sq

  Pos->Inv : {q : ℚ} -> Pos q -> ℚInv q
  Pos->Inv p = NonZero->¬Zero {D = ℚ} (inj-l p)

  Neg->Inv : {q : ℚ} -> Neg q -> ℚInv q
  Neg->Inv p = NonZero->¬Zero {D = ℚ} (inj-r p)


  Pos-1r : Pos 1r
  Pos-1r = same-sign-ℚ' pos-sign 1r' (Pos-ℕ⁺->ℚ' (1 , tt))

abstract

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
    module _ where
      n' = (ℕ->ℚ ⟨ n ⟩)
      i = (Pos->Inv (Pos-ℕ⁺->ℚ n))



ℚ⁺ : Type₀
ℚ⁺ = Σ ℚ Pos
ℚ⁻ : Type₀
ℚ⁻ = Σ ℚ Neg

ℚ⁰⁺ : Type₀
ℚ⁰⁺ = Σ ℚ (0# ≤_)
ℚ⁰⁻ : Type₀
ℚ⁰⁻ = Σ ℚ (_≤ 0#)


opaque
  unfolding ℚ

  r+₁-preserves-< : (a b c : ℚ) -> b < c -> (a + b) < (a + c)
  r+₁-preserves-< a b c (ℚ<-cons b<c) =
    SetQuotientElim.elimProp3
      {C3 = \a b c -> ℚ<-raw b c -> (a + b) < (a + c)}
      (\_ _ _ -> isPropΠ (\_ -> isProp-<))
      convert
      a b c b<c
    where
    convert : (a b c : ℚ') -> ℚ<-raw (ℚ'->ℚ b) (ℚ'->ℚ c) ->
              ((ℚ'->ℚ a) + (ℚ'->ℚ b)) < ((ℚ'->ℚ a) + (ℚ'->ℚ c))
    convert a b c b<c =
      ℚ<-cons
        (transport (sym (cong2 ℚ<-raw r+-eval r+-eval >=> ℚ<-raw-eval))
                   (r+'₁-preserves-< a b c (transport ℚ<-raw-eval b<c)))

  r*₁-preserves-< : (a b c : ℚ) -> 0r < a -> b < c -> (a * b) < (a * c)
  r*₁-preserves-< a b c (ℚ<-cons 0<a) (ℚ<-cons b<c) =
    SetQuotientElim.elimProp3
      {C3 = \a b c -> ℚ<-raw 0r a -> ℚ<-raw b c -> (a * b) < (a * c)}
      (\_ _ _ -> isPropΠ2 (\_ _ -> isProp-<))
      convert
      a b c 0<a b<c
    where
    convert : (a b c : ℚ') -> ℚ<-raw 0r (ℚ'->ℚ a) -> ℚ<-raw (ℚ'->ℚ b) (ℚ'->ℚ c) ->
              ((ℚ'->ℚ a) * (ℚ'->ℚ b)) < ((ℚ'->ℚ a) * (ℚ'->ℚ c))
    convert a b c 0<a b<c =
      ℚ<-cons (transport (sym ℚ<-raw-eval >=> cong2 ℚ<-raw (sym r*-eval) (sym r*-eval))
                         (r*'₁-preserves-< a b c (transport ℚ<-raw-eval 0<a) (transport ℚ<-raw-eval b<c)))

instance
  LinearlyOrderedAdditiveStr-ℚ : LinearlyOrderedAdditiveStr useⁱ useⁱ
  LinearlyOrderedAdditiveStr-ℚ =
    LinearlyOrderedAdditiveStr-Dec< (r+₁-preserves-< _ _ _)

  LinearlyOrderedSemiringStr-ℚ : LinearlyOrderedSemiringStr Semiring-ℚ useⁱ
  LinearlyOrderedSemiringStr-ℚ = LinearlyOrderedSemiringStr-Ring
    (r*₁-preserves-< _ _ _)

  StronglyLinearlyOrderedSemiringStr-ℚ : StronglyLinearlyOrderedSemiringStr Semiring-ℚ _
  StronglyLinearlyOrderedSemiringStr-ℚ =
    StronglyLinearlyOrderedSemiringStr-Dec<

module _ where
  private
    module M where
      abstract
        r+₁-preserves-≤ : (a b c : ℚ) -> b ≤ c -> (a + b) ≤ (a + c)
        r+₁-preserves-≤ a = ℚ≤-elim (isProp-≤ {D = ℚ}) f< f=
          where
          module _ where
            f< : {b c : ℚ} -> b < c -> _
            f< = weaken-< ∘ r+₁-preserves-< a _ _

            f= : {b c : ℚ} -> b == c -> _
            f= = path-≤ ∘ (cong (a +_))
  open M public


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

  r*₁-preserves-≤ : (a b c : ℚ) -> 0r ≤ a -> b ≤ c -> (a * b) ≤ (a * c)
  r*₁-preserves-≤ a b c 0≤a b≤c =
    ℚ0≤-elim {P = \a -> (a * b) ≤ (a * c)}
       (isProp-≤ {D = ℚ}) f< f= a 0≤a
    where
    0≤bc : 0r ≤ diff b c
    0≤bc = subst2 _ℚ≤_ (+-commute >=> +-inverse) +-commute (r+₁-preserves-≤ (- b) b c b≤c)

    f= : {a : ℚ} -> 0r == a -> (a * b) ≤ (a * c)
    f= 0=a = path-≤ (*-left (sym 0=a) >=> *-left-zero >=> sym *-left-zero >=> *-left 0=a)

    f< : {a : ℚ} -> 0r < a -> (a * b) ≤ (a * c)
    f< {a} 0<a =
      subst2 _ℚ≤_ +-right-zero
        (+-right (*-distrib-diff-left >=> +-commute) >=>
         sym +-assoc >=>
         +-left +-inverse >=>
         +-left-zero)
        (r+₁-preserves-≤ (a * b) 0r (a * diff b c) 0≤abc)
      where

      g= : {bc : ℚ} -> 0r == bc -> 0r ≤ (a * bc)
      g= 0=bc = path-≤ (sym *-right-zero >=> *-right 0=bc)

      g< : {bc : ℚ} -> 0r < bc -> 0r ≤ (a * bc)
      g< 0<bc = weaken-< (*-preserves-0< 0<a 0<bc)

      0≤abc : 0r ≤ (a * (diff b c))
      0≤abc = ℚ0≤-elim (isProp-≤ {D = ℚ}) g< g= (diff b c) 0≤bc


instance
  PartiallyOrderedAdditiveStr-ℚ : PartiallyOrderedAdditiveStr useⁱ useⁱ
  PartiallyOrderedAdditiveStr-ℚ = record
    { +₁-preserves-≤ = r+₁-preserves-≤ _ _ _
    }

  PartiallyOrderedSemiringStr-ℚ : PartiallyOrderedSemiringStr Semiring-ℚ useⁱ
  PartiallyOrderedSemiringStr-ℚ =
    PartiallyOrderedSemiringStr-Ring (weaken-< Pos-1r) (r*₁-preserves-≤ _ _ _)


-- Compatibility functions

abstract
  Zero-path : (q : ℚ) -> Zeroℚ q -> q == 0r
  Zero-path _ p = p

  r--flips-sign : (q : ℚ) (s : Sign) -> (isSignℚ s q) -> (isSignℚ (s⁻¹ s) (r- q))
  r--flips-sign q pos-sign 0<q = minus-flips-0< 0<q
  r--flips-sign q zero-sign q=0 = cong -_ q=0 >=> minus-zero
  r--flips-sign q neg-sign q<0 = minus-flips-<0 q<0

  r--NonNeg : {q1 : ℚ} -> NonNeg q1 -> NonPos (r- q1)
  r--NonNeg (inj-l s) = (inj-l (r--flips-sign _ pos-sign s))
  r--NonNeg (inj-r s) = (inj-r (r--flips-sign _ zero-sign s))

  r--NonPos : {q1 : ℚ} -> NonPos q1 -> NonNeg (r- q1)
  r--NonPos (inj-l s) = (inj-l (r--flips-sign _ neg-sign s))
  r--NonPos (inj-r s) = (inj-r (r--flips-sign _ zero-sign s))

  NonNeg-0≤ : (q : ℚ) -> NonNeg q -> 0r ≤ q
  NonNeg-0≤ _ (inj-l pq) = weaken-ℚ< pq
  NonNeg-0≤ q (inj-r zq) = subst (_ℚ≤ q) zq (refl-≤ {D = ℚ})

  NonPos-≤0 : (q : ℚ) -> NonPos q -> q ≤ 0r
  NonPos-≤0 _ (inj-l nq) = weaken-ℚ< nq
  NonPos-≤0 q (inj-r zq) = subst (q ℚ≤_) zq (refl-≤ {D = ℚ})

  0≤-NonNeg : (q : ℚ) -> 0r ≤ q -> NonNeg q
  0≤-NonNeg q 0≤q = ℚ0≤-elim (isProp-NonNeg {D = ℚ} _) inj-l (inj-r ∘ sym) q 0≤q

  ≤0-NonPos : (q : ℚ) -> q ≤ 0r -> NonPos q
  ≤0-NonPos q q≤0 =
    subst (NonPos {D = ℚ}) minus-double-inverse (r--NonNeg (0≤-NonNeg (r- q) (minus-flips-≤0 q≤0)))

  Pos-0< : (q : ℚ) -> Pos q -> 0r < q
  Pos-0< q 0<q = 0<q

  Neg-<0 : (q : ℚ) -> Neg q -> q < 0r
  Neg-<0 q q<0 = q<0

  0<-Pos : (q : ℚ) -> 0r < q -> Pos q
  0<-Pos q 0<q = 0<q

  <0-Neg : (q : ℚ) -> q < 0r -> Neg q
  <0-Neg q q<0 = q<0

  NonPos≤NonNeg : {q r : ℚ} -> NonPos q -> NonNeg r -> q ℚ≤ r
  NonPos≤NonNeg np-q nn-r = trans-≤ {D = ℚ} (NonPos-≤0 _ np-q) (NonNeg-0≤ _ nn-r)

  NonNeg-≤ : (a b : ℚ) -> NonNeg a -> a ℚ≤ b -> NonNeg b
  NonNeg-≤ a b (inj-l 0<a) a≤b = 0≤-NonNeg _ (trans-≤ {D = ℚ} (weaken-< 0<a) a≤b)
  NonNeg-≤ a b (inj-r za) a≤b = 0≤-NonNeg _ (trans-=-≤ (sym (Zero-path a za)) a≤b)

  NonPos-≤ : (a b : ℚ) -> NonPos b -> a ℚ≤ b -> NonPos a
  NonPos-≤ a b (inj-l b<0) a≤b = ≤0-NonPos _ (trans-≤ {D = ℚ} a≤b (weaken-< b<0))
  NonPos-≤ a b (inj-r zb) a≤b = ≤0-NonPos _ (trans-≤-= a≤b (Zero-path b zb))

  Pos-≤ : (a b : ℚ) -> Pos a -> a ℚ≤ b -> Pos b
  Pos-≤ a b 0<a a≤b = trans-<-≤ 0<a a≤b

  Neg-≤ : (a b : ℚ) -> Neg b -> a ℚ≤ b -> Neg a
  Neg-≤ a b b<0 a≤b = trans-≤-< a≤b b<0

  Pos-< : (a b : ℚ) -> NonNeg a -> a ℚ< b -> Pos b
  Pos-< a b nn a<b = trans-≤-< (NonNeg-0≤ _ nn) a<b

  Neg-< : (a b : ℚ) -> NonPos b -> a ℚ< b -> Neg a
  Neg-< a b np a<b = trans-<-≤ a<b (NonPos-≤0 _ np)

  r*-Pos-Pos : {q1 q2 : ℚ} -> Pos q1 -> Pos q2 -> Pos (q1 r* q2)
  r*-Pos-Pos p1 p2 = *-preserves-0< p1 p2

  r*-Pos-Neg : {q1 q2 : ℚ} -> Pos q1 -> Neg q2 -> Neg (q1 r* q2)
  r*-Pos-Neg {q1} {q2} p1 n2 =
    subst ((q1 * q2) <_) *-right-zero (*₁-preserves-< p1 n2)

  r*-Neg-Pos : {q1 q2 : ℚ} -> Neg q1 -> Pos q2 -> Neg (q1 r* q2)
  r*-Neg-Pos n1 p2 = subst (Neg {D = ℚ}) *-commute (r*-Pos-Neg p2 n1)

  r*-Neg-Neg : {q1 q2 : ℚ} -> Neg q1 -> Neg q2 -> Pos (q1 r* q2)
  r*-Neg-Neg {q1} {q2} n1 n2 = subst (_< (q1 * q2)) *-right-zero (*₁-flips-< n1 n2)


  r*-NonNeg-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r* q2)
  r*-NonNeg-NonNeg nn1 nn2 = 0≤-NonNeg _ (*-preserves-0≤ (NonNeg-0≤ _ nn1) (NonNeg-0≤ _ nn2))

  r*-NonNeg-NonPos : {q1 q2 : ℚ} -> NonNeg q1 -> NonPos q2 -> NonPos (q1 r* q2)
  r*-NonNeg-NonPos {q1} {q2} nn1 np2 = ≤0-NonPos _ q1q2≤0
    where
    module _ where
      q1q2≤0 : (q1 * q2) ≤ 0r
      q1q2≤0 = subst ((q1 * q2) ≤_) *-right-zero (*₁-preserves-≤ (NonNeg-0≤ _ nn1) (NonPos-≤0 _ np2))

  r*-NonPos-NonNeg : {q1 q2 : ℚ} -> NonPos q1 -> NonNeg q2 -> NonPos (q1 r* q2)
  r*-NonPos-NonNeg np nn = subst (NonPos {D = ℚ}) *-commute (r*-NonNeg-NonPos nn np)

  r*-NonPos-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonNeg (q1 r* q2)
  r*-NonPos-NonPos {q1} {q2} nn1 np2 = 0≤-NonNeg _ 0≤q1q2
    where
    module _ where
      0≤q1q2 : 0r ≤ (q1 * q2)
      0≤q1q2 = subst (_≤ (q1 * q2)) *-right-zero (*₁-flips-≤ (NonPos-≤0 _ nn1) (NonPos-≤0 _ np2))



  r+-NonNeg-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r+ q2)
  r+-NonNeg-NonNeg {q1} {q2} nn1 nn2 = 0≤-NonNeg (q1 + q2)
    (subst (_≤ (q1 + q2)) +-left-zero (+-preserves-≤ (NonNeg-0≤ q1 nn1) (NonNeg-0≤ q2 nn2)))

  r+-NonPos-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonPos (q1 r+ q2)
  r+-NonPos-NonPos {q1} {q2} np1 np2 = ≤0-NonPos (q1 + q2)
    (subst ((q1 + q2) ≤_) +-left-zero (+-preserves-≤ (NonPos-≤0 q1 np1) (NonPos-≤0 q2 np2)))


  r*-preserves-Pos : (q1 q2 : ℚ) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)
  r*-preserves-Pos _ _ = r*-Pos-Pos


  r+-preserves-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonPos (q1 r+ q2)
  r+-preserves-NonPos = r+-NonPos-NonPos

  r+-preserves-Pos : (q1 q2 : ℚ) -> Pos q1 -> Pos q2 -> Pos (q1 r+ q2)
  r+-preserves-Pos q1 q2 p1 p2 =
    subst (_< (q1 + q2)) +-left-zero (+-preserves-< p1 p2)

  r+-preserves-Neg : (q1 q2 : ℚ) -> Neg q1 -> Neg q2 -> Neg (q1 r+ q2)
  r+-preserves-Neg q1 q2 p1 p2 =
    subst ((q1 + q2) <_) +-left-zero (+-preserves-< p1 p2)



  r*-ZeroFactor : {q1 q2 : ℚ} -> Zero (q1 r* q2) -> Zero q1 ⊎ Zero q2
  r*-ZeroFactor {q1} {q2} zp =
    handle (fst (decide-sign q1)) (fst (decide-sign q2)) (snd (decide-sign q1)) (snd (decide-sign q2))
    where
    module _ where
      handle : (s1 s2 : Sign) -> isSignℚ s1 q1 -> isSignℚ s2 q2 -> Zero q1 ⊎ Zero q2
      handle zero-sign _         z1 _ = inj-l z1
      handle pos-sign  zero-sign p1 z2 = inj-r z2
      handle neg-sign  zero-sign n1 z2 = inj-r z2
      handle pos-sign  pos-sign  p1 p2 =
        bot-elim (NonZero->¬Zero {D = ℚ} (inj-l (*-preserves-0< p1 p2)) zp)
      handle pos-sign  neg-sign  p1 n2 = bot-elim (NonZero->¬Zero {D = ℚ} (inj-r p<0) zp)
        where
        p<0 : (q1 * q2) < 0r
        p<0 = subst ((q1 * q2) <_) *-right-zero (*₁-preserves-< p1 n2)
      handle neg-sign  pos-sign  n1 p2 = bot-elim (NonZero->¬Zero {D = ℚ} (inj-r p<0) zp)
        where
        p<0 : (q1 * q2) < 0r
        p<0 = subst ((q1 * q2) <_) *-left-zero (*₂-preserves-< n1 p2)
      handle neg-sign  neg-sign  n1 n2 = bot-elim (NonZero->¬Zero  {D = ℚ}(inj-l 0<p) zp)
        where
        0<p : 0r < (q1 * q2)
        0<p = subst (_< (q1 * q2)) *-right-zero (*₁-flips-< n1 n2)


  r*₁-preserves-sign : (q : ℚ⁺) (r : ℚ) {s : Sign} -> isSignℚ s r -> isSignℚ s (⟨ q ⟩ r* r)
  r*₁-preserves-sign (q , pq) r {pos-sign} pr = *-preserves-0< pq pr
  r*₁-preserves-sign (q , pq) r {zero-sign} zr = *-right zr >=> *-right-zero
  r*₁-preserves-sign (q , pq) r {neg-sign} nr = r*-Pos-Neg pq nr

  r*₁-flips-sign : (q : ℚ⁻) (r : ℚ) {s : Sign} -> isSignℚ s r -> isSignℚ (s⁻¹ s) (⟨ q ⟩ r* r)
  r*₁-flips-sign (q , nq) r {pos-sign} pr = r*-Neg-Pos nq pr
  r*₁-flips-sign (q , nq) r {zero-sign} zr = *-right zr >=> *-right-zero
  r*₁-flips-sign (q , nq) r {neg-sign} nr = r*-Neg-Neg nq nr


  r1/-preserves-Pos : (q : ℚ) -> (i : ℚInv q) -> Pos q -> Pos (r1/ q i)
  r1/-preserves-Pos q i pq = handle (decide-sign qi)
    where
    module _ where
      qi = (r1/ q i)
      handle : Σ[ s ∈ Sign ] (isSign s qi) -> Pos qi
      handle (pos-sign , pqi) = pqi
      handle (zero-sign , zqi) = bot-elim (NonPos->¬Pos {D = ℚ} (inj-r z1) Pos-1r)
        where
        z1 : Zero 1r
        z1 = subst Zero (*-commute >=> r1/-inverse q i) (r*₁-preserves-sign (q , pq) qi {zero-sign} zqi)
      handle (neg-sign , nqi) = bot-elim (NonPos->¬Pos {D = ℚ} (inj-l n1) Pos-1r)
        where
        n1 : Neg 1r
        n1 = subst Neg (*-commute >=> r1/-inverse q i) (r*₁-preserves-sign (q , pq) qi {neg-sign} nqi)



  r1/-preserves-Neg : (q : ℚ) -> (i : ℚInv q) -> Neg q -> Neg (r1/ q i)
  r1/-preserves-Neg q i nq = handle (decide-sign qi)
    where
    module _ where
      qi = (r1/ q i)
      handle : Σ[ s ∈ Sign ] (isSign s qi) -> Neg qi
      handle (neg-sign , nqi) = nqi
      handle (zero-sign , zqi) = bot-elim (NonPos->¬Pos {D = ℚ} (inj-r z1) Pos-1r)
        where
        z1 : Zero 1r
        z1 = subst Zero (*-commute >=> r1/-inverse q i) (r*₁-flips-sign (q , nq) qi {zero-sign} zqi)
      handle (pos-sign , pqi) = bot-elim (NonPos->¬Pos {D = ℚ} (inj-l n1) Pos-1r)
        where
        n1 : Neg 1r
        n1 = subst Neg (*-commute >=> r1/-inverse q i) (r*₁-flips-sign (q , nq) qi {pos-sign} pqi)

  Pos-1/ℕ : (n : Nat⁺) -> Pos (1/ℕ n)
  Pos-1/ℕ n = subst Pos (sym (1/ℕ-inv-path n)) (r1/-preserves-Pos (ℕ->ℚ ⟨ n ⟩) _ (Pos-ℕ⁺->ℚ n))

  NonNeg-diffℚ : (a b : ℚ) -> a ≤ b -> NonNeg (diff a b)
  NonNeg-diffℚ a b a≤b =
    0≤-NonNeg _ (subst (_≤ (diff a b)) +-inverse (+₂-preserves-≤ a≤b))

  NonNeg-diffℚ⁻ : (a b : ℚ) -> NonNeg (diff a b) -> a ≤ b
  NonNeg-diffℚ⁻ a b nn =
    subst2 _ℚ≤_ +-right-zero diff-step (+₁-preserves-≤ (NonNeg-0≤ _ nn))

  Pos-diffℚ : (a b : ℚ) -> a < b -> Pos (diff a b)
  Pos-diffℚ a b a<b =
    subst (_< (diff a b)) +-inverse (+₂-preserves-< a<b)

  Pos-diffℚ⁻ : (a b : ℚ) -> Pos (diff a b) -> a < b
  Pos-diffℚ⁻ a b p =
    subst2 _<_ +-right-zero diff-step (+₁-preserves-< p)


  dense-< : Dense _ℚ<_
  dense-< {x} {y} lt = ∣ z , (Pos-diffℚ⁻ _ _ pos-d3 , Pos-diffℚ⁻ _ _ pos-d4) ∣
    where
    module _ where
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
    subst (_< (a + b)) +-right-zero (+₁-preserves-< pos-b)

  r+-Neg->order : (a : ℚ) (b : Σ ℚ Negℚ) -> a > (a r+ ⟨ b ⟩)
  r+-Neg->order a (b , neg-b) =
    subst (_> (a + b)) +-right-zero (+₁-preserves-< neg-b)


abstract
  ℕ->ℚ-preserves-< : {a b : Nat} -> a < b -> (ℕ->ℚ a) < (ℕ->ℚ b)
  ℕ->ℚ-preserves-< a<b =
    ℚ<-cons (transport (sym ℚ<-raw-eval) (ℕ->ℚ'-preserves-< a<b))

  ℕ->ℚ-preserves-≤ : {a b : Nat} -> a ≤ b -> (ℕ->ℚ a) ≤ (ℕ->ℚ b)
  ℕ->ℚ-preserves-≤ a≤b =
    ℚ≤-cons (transport (sym ℚ≤-raw-eval) (ℕ->ℚ'-preserves-≤ a≤b))

  1/ℕ-flips-order : (a b : Nat⁺) -> ⟨ a ⟩ < ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
  1/ℕ-flips-order a@(a' , _) b@(b' , _) lt = subst2 _<_ b-path a-path ab*<
    where
    module _ where
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
      ab*< = *₁-preserves-< pos-ab (ℕ->ℚ-preserves-< lt)

  1/ℕ-flips-≤ : (a b : Nat⁺) -> ⟨ a ⟩ ≤ ⟨ b ⟩ -> 1/ℕ b ≤ 1/ℕ a
  1/ℕ-flips-≤ a@(a' , _) b@(b' , _) lt = subst2 _≤_ b-path a-path ab*≤
    where
    module _ where
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

      ab*≤ : (ab r* (ℕ->ℚ a')) ≤ (ab r* (ℕ->ℚ b'))
      ab*≤ = *₁-preserves-≤ (weaken-< pos-ab) (ℕ->ℚ-preserves-≤ lt)

  1/ℕ≤1 : (a : Nat⁺) -> 1/ℕ a ≤ 1#
  1/ℕ≤1 a@(suc _ , _) =
    trans-≤-= (1/ℕ-flips-≤ 1⁺ a nat.order.zero-<) 1/ℕ-1

  private
    zero-diff->path : (x y : ℚ) -> Zeroℚ (y r+ (r- x)) -> x == y
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
    module _ where
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
    handle : NonNeg (diff a' b') -> (r1/ b' (Pos->Inv pos-b')) ℚ≤ (r1/ a' (Pos->Inv pos-a'))
    handle (inj-l pd) = weaken-< (r1/-Pos-flips-order a b (Pos-diffℚ⁻ a' b' pd))
    handle (inj-r zd) = path-≤ (sym path)
      where
      a==b : a' == b'
      a==b = zero-diff->path a' b' zd

      path : (r1/ a' (Pos->Inv pos-a')) == (r1/ b' (Pos->Inv pos-b'))
      path i = (r1/ (a==b i) (Pos->Inv (isProp->PathPᵉ (\ j -> isProp-Pos (a==b j)) pos-a' pos-b' i)))



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
  n⁺d⁺->ℚ n d = ℚ'->ℚ (n⁺d⁺->ℚ' n d)

  n⁺d⁺->ℚ⁺ : (n d : Nat⁺) -> ℚ⁺
  n⁺d⁺->ℚ⁺ n d = n⁺d⁺->ℚ n d ,
           same-sign-ℚ' pos-sign _ (is-signℚ' (i.*-Pos-Pos (i.Pos'->Pos (snd n)) (i.Pos'->Pos (snd d))))


  opaque
    unfolding ℚ

    ℚ⁺-elimProp :
      {ℓ : Level} -> {P : Pred ℚ⁺ ℓ} -> ((q : ℚ⁺) -> isProp (P q)) ->
      ((n d : Nat⁺) -> P (n⁺d⁺->ℚ⁺ n d)) ->
      (q : ℚ⁺) -> P q
    ℚ⁺-elimProp {P = P} isProp-P f (q , pos-q) =
      SetQuotientElim.elimProp (\q -> isPropΠ (\pos-q -> isProp-P (q , pos-q))) handle q pos-q
      where
      find-rep : (q' : ℚ') -> (Pos q') -> Σ[ n ∈ Nat⁺ ] (Σ[ d ∈ Nat⁺ ] (n⁺d⁺->ℚ' n d r~ q'))
      find-rep (record { denominator = i.zero-int ; NonZero-denominator = nz }) =
        bot-elim (i.NonZero->!=0 nz refl)
      find-rep (record { numerator = (i.pos n') ; denominator = (i.pos d') }) _ =
        ((suc n' , tt) , (suc d' , tt) , refl)
      find-rep (record { numerator = (i.zero-int) ; denominator = (i.pos d') }) p =
        bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg refl-≤ (weaken-< 0<pos)) (isSignℚ'.v p))
      find-rep (record { numerator = (i.nonneg _) ; denominator = (i.neg d') }) p =
        bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos 0≤nonneg (weaken-< neg<0)) (isSignℚ'.v p))
      find-rep (record { numerator = (i.neg _) ; denominator = (i.pos d') }) p =
        bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (weaken-< neg<0) (weaken-< 0<pos)) (isSignℚ'.v p))
      find-rep (record { numerator = (i.neg n') ; denominator = (i.neg d') }) _ =
        ((suc n' , tt) , (suc d' , tt) , minus-extract-right >=> sym minus-extract-left )

      handle : (q' : ℚ') -> (pos-q : (Pos (ℚ'->ℚ q'))) -> P (ℚ'->ℚ q' , pos-q)
      handle q' pos-q' = subst P path (f n d)
        where
        rep : Σ[ n ∈ Nat⁺ ] (Σ[ d ∈ Nat⁺ ] (n⁺d⁺->ℚ' n d r~ q'))
        rep = find-rep q' (same-sign-ℚ'⁻ _ _ pos-q')
        n : Nat⁺
        n = fst rep
        d : Nat⁺
        d = fst (snd rep)
        nd~ : n⁺d⁺->ℚ' n d r~ q'
        nd~ = snd (snd rep)

        path : (n⁺d⁺->ℚ⁺ n d) == (ℚ'->ℚ q' , pos-q')
        path = ΣProp-path (\{x} -> isProp-Pos x) (r~->path _ _ nd~)


  1/ℕ-<-step1 : (n d : Nat⁺) -> (1/ℕ' d) ℚ'≤ (n⁺d⁺->ℚ' n d)
  1/ℕ-<-step1 n@(n'@(suc n'') , _)  d@(d' , pos-d) = ℚ'≤-cons ans
    where
    x1 = same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d))
    x2 = ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))

    NonNeg-numer : i.NonNeg (int n' + (- (int 1)))
    NonNeg-numer = trans-≤-= 0≤nonneg (sym ℤ+-eval >=> +-commute)

    ans2 : NonNeg (same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)))
    ans2 = NonNeg-nd->ℚ' (*-preserves-0≤ NonNeg-numer (weaken-< (i.Pos'->Pos pos-d)))

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
      handle n d (m , p) = m , (ℚ≤-cons (transport (sym ℚ≤-raw-eval) p))
