{-# OPTIONS --cubical --safe --exact-split #-}

module set-quotient where

open import base
open import equality
open import equivalence
open import funext
open import hlevel
open import sigma
open import univalence
open import isomorphism
open import relation

data _/_ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (R : A -> A -> Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  [_] : (a : A) -> A / R
  eq/ : (a b : A) -> (r : R a b) -> [ a ] == [ b ]
  squash/ : isSet (A / R)

module SetQuotientElim {ℓA ℓR : Level} (A : Type ℓA) (R : A -> A -> Type ℓR) where
  private
    variable
      ℓ : Level
      B : Type ℓ
      C : A / R -> Type ℓ
      C2 : A / R ->  A / R -> Type ℓ
      C3 : A / R -> A / R ->  A / R -> Type ℓ

  rec : (isSetB : isSet B) (f : A -> B)
        (f~ : (a1 a2 : A) (r : R a1 a2) -> (f a1 == f a2)) ->
        A / R -> B
  rec isSetB f f~ [ a ] = f a
  rec isSetB f f~ (eq/ a1 a2 r i) = f~ a1 a2 r i
  rec isSetB f f~ (squash/ a1 a2 p1 p2 i j) = isSetB (g a1) (g a2) (cong g p1) (cong g p2) i j
    where
    g = rec isSetB f f~

  elim : (isSetC : (ar : A / R) -> isSet (C ar)) ->
         (f : (a : A) -> C [ a ]) ->
         (f~ : (a1 a2 : A) (r : R a1 a2) ->
               PathP (\i -> C (eq/ a1 a2 r i)) (f a1) (f a2)) ->
         (ar : A / R) -> C ar
  elim isSetC f f~ [ a ] = f a
  elim isSetC f f~ (eq/ a1 a2 r i) = f~ a1 a2 r i
  elim isSetC f f~ (squash/ a1 a2 p1 p2 i j) =
    isOfHLevel->isOfHLevelDep 2 isSetC (g a1) (g a2) (cong g p1) (cong g p2) (squash/ a1 a2 p1 p2) i j
    where
    g = elim isSetC f f~

  elimProp : (isPropC : (ar : A / R) -> isProp (C ar)) ->
             (f : (a : A) -> C [ a ]) ->
             (ar : A / R) -> C ar
  elimProp {C = C} isPropC f =
    elim (\ar -> (isProp->isSet (isPropC ar))) f f~
    where
    f~ : (a1 a2 : A) (r : R a1 a2) -> PathP (\i -> C (eq/ a1 a2 r i)) (f a1) (f a2)
    f~ a1 a2 r = isProp->PathP (\i -> isPropC (eq/ a1 a2 r i)) (f a1) (f a2)


  elimProp2 : (isPropC2 : (ar1 ar2 : A / R) -> isProp (C2 ar1 ar2)) ->
              (f : (a1 a2 : A) -> C2 [ a1 ] [ a2 ]) ->
              (ar1 ar2 : A / R ) -> C2 ar1 ar2
  elimProp2 {C2 = C2} isPropC2 f =
    elimProp (\a1 -> isPropΠ (isPropC2 a1))
             (\a1 -> (elimProp (isPropC2 [ a1 ]) (f a1)))

  elimProp3 : (isPropC3 : (ar1 ar2 ar3 : A / R) -> isProp (C3 ar1 ar2 ar3)) ->
              (f : (a1 a2 a3 : A) -> C3 [ a1 ] [ a2 ] [ a3 ]) ->
              (ar1 ar2 ar3 : A / R ) -> C3 ar1 ar2 ar3
  elimProp3 {C3 = C3} isPropC3 f =
    elimProp (\a1 -> isPropΠ2 (isPropC3 a1))
             (\a1 -> (elimProp2 (isPropC3 [ a1 ]) (f a1)))

  rec2 : (isSetB : isSet B) (f : A -> A -> B)
         (f~₁ : (y x1 x2 : A) (r : R x1 x2) -> (f x1 y == f x2 y)) ->
         (f~₂ : (x y1 y2 : A) (r : R y1 y2) -> (f x y1 == f x y2)) ->
         A / R -> A / R -> B
  rec2 {B = B} isSetB f f~₁ f~₂ =
    rec (isSetΠ (\_ -> isSetB)) g g~
    where
    g : A -> A / R -> B
    g a = rec isSetB (f a) (f~₂ a)

    g~' : (x1 x2 : A) -> (r : R x1 x2) -> (y : A / R) -> g x1 y == g x2 y
    g~' x1 x2 r = elimProp (\i -> isSetB _ _) (\y -> f~₁ y x1 x2 r)

    g~ : (a1 a2 : A) -> (r : R a1 a2) -> g a1 == g a2
    g~ a1 a2 r = funExt (g~' a1 a2 r)


  pathRec : (isPropValued R) -> (isEquivRel R) -> (a1 a2 : A) ->
            Path (A / R) [ a1 ] [ a2 ] -> R a1 a2
  pathRec isProp-R (equivRel refl-R sym-R trans-R) a1 a2 p = transport a1a1=a1a2 refl-R
    where
    path : (A / R) -> hProp ℓR
    path = rec isSet-hProp prop1 prop1/eq
      where
      prop1 : A -> hProp ℓR
      prop1 a = R a1 a , isProp-R _ _
      prop1/eq : (a3 a4 : A) -> (r : R a3 a4) -> prop1 a3 == prop1 a4
      prop1/eq a3 a4 r34 = ΣProp-path (isProp-isOfHLevel 1) (ua (isoToEquiv i))
        where
        open Iso
        i : Iso (R a1 a3) (R a1 a4)
        i .fun r13 = trans-R r13 r34
        i .inv r14 = trans-R r14 (sym-R r34)
        i .rightInv _ = isProp-R _ _ _ _
        i .leftInv _ = isProp-R _ _ _ _

    a1a1=a1a2 : R a1 a1 == R a1 a2
    a1a1=a1a2 = cong fst (cong path p)