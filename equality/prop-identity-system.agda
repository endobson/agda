{-# OPTIONS --cubical --safe --exact-split #-}

module equality.prop-identity-system where

open import base
open import equality
open import equality.identity-system
open import hlevel
open import relation

record PropIdentitySystem {ℓA : Level} (A : Type ℓA) (ℓ : Level) : Type (ℓ-max (ℓ-suc ℓ) ℓA) where
  field
    R' : (x y : A) -> hProp ℓ

  R : Rel A ℓ
  R x y = fst (R' x y)

  field
    r : (a : A) -> R a a
    to-path : {a1 a2 : A} -> R a1 a2 -> a1 == a2

  isIdSys : isIdentitySystem R r
  isIdSys .isIdentitySystem.to-path = to-path
  isIdSys .isIdentitySystem.to-path-over _ =
    isProp->PathP (\_ -> snd (R' _ _))

  opaque
    isSet-A : isSet A
    isSet-A = idSys-isOfHLevel isIdSys 1 (\x y -> snd (R' x y))

  opaque
    distinct : {a1 a2 : A} -> ¬ (R a1 a2) -> a1 != a2
    distinct {a1} {a2} ¬R p = ¬R (subst (R a1) p (r a1))
