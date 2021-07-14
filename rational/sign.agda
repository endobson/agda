{-# OPTIONS --cubical --safe --exact-split #-}

module rational.sign where

open import base
open import equality
open import hlevel
open import isomorphism
open import rational
open import relation
open import semiring
open import ring.implementations
open import set-quotient
open import sign
open import sign.instances.fraction
open import fraction.sign
open import sigma
open import univalence


private
  isSign-full : Sign -> Rational -> hProp ℓ-zero
  isSign-full s = RationalElim.elim (\_ -> isSet-hProp) val preserved
    where
    val : Rational' -> hProp ℓ-zero
    val r = isSign s r , isProp-isSign s r
    preserved : (a b : Rational') -> (a r~ b) -> val a == val b
    preserved a b a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (isSign s a) (isSign s b)
      i .fun p = r~-preserves-sign {a} {b} {s} p a~b
      i .inv p = r~-preserves-sign {b} {a} {s} p (sym a~b)
      i .rightInv p = isProp-isSign s _ _ p
      i .leftInv p = isProp-isSign s _ _ p

  isSignℚ-base : Sign -> Pred Rational ℓ-zero
  isSignℚ-base s r = fst (isSign-full s r)

  isProp-isSignℚ-base : (s : Sign) -> (r : Rational) -> isProp (isSignℚ-base s r)
  isProp-isSignℚ-base s r = snd (isSign-full s r)

record isSignℚ (s : Sign) (q : ℚ) : Type₀ where
  constructor is-signℚ
  field
    v : isSignℚ-base s q

private
  isProp-isSignℚ : (s : Sign) -> (r : Rational) -> isProp (isSignℚ s r)
  isProp-isSignℚ s r p1 p2 = cong is-signℚ (isProp-isSignℚ-base s r (isSignℚ.v p1) (isSignℚ.v p2))

  isSignℚ-unique : (r : Rational) (s1 s2 : Sign)-> isSignℚ s1 r -> isSignℚ s2 r -> s1 == s2
  isSignℚ-unique r s1 s2 =
    RationalElim.elimProp
      {C = \r -> isSignℚ s1 r -> isSignℚ s2 r -> s1 == s2}
      (\_ -> isPropΠ2 (\ _ _ -> isSet-Sign s1 s2))
      (\r v1 v2 -> isSign-unique r s1 s2 (isSignℚ.v v1) (isSignℚ.v v2))
      r

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
    decide-signℚ =
      RationalElim.elimProp
        (\q -> uniqueProp->isPropΣ (isSign-unique q) (\s -> isProp-isSign s q))
        (\q -> handle (decide-sign q))
      where
        handle : {q : ℚ'} -> Σ[ s ∈ Sign ] (isSign s q) -> Σ[ s ∈ Sign ] (isSign s [ q ])
        handle (s , sq) = (s , is-signℚ sq)

instance
  DecidableSignStr-ℚ : DecidableSignStr SignStr-ℚ
  DecidableSignStr-ℚ = record
    { decide-sign = decide-signℚ
    }


NonNeg-ℚ'->ℚ : {q : Rational'} -> NonNeg q -> NonNeg [ q ]
NonNeg-ℚ'->ℚ (inj-l p) = inj-l (is-signℚ p)
NonNeg-ℚ'->ℚ (inj-r p) = inj-r (is-signℚ p)
