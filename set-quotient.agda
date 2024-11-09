{-# OPTIONS --cubical --safe --exact-split #-}

module set-quotient where

open import base
open import discrete
open import equality-path
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import relation
open import sigma.base
open import truncation
open import univalence

data _/_ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (R : A -> A -> Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  [_] : (a : A) -> A / R
  eq/ : (a b : A) -> (r : R a b) -> [ a ] == [ b ]
  -- squash/ : isSet (A / R)
  squash/ : (a b : A / R) -> (p q : a == b) -> p == q -- isSet (A / R)

module SetQuotientElimᵉ {ℓA ℓR : Level} (A : Type ℓA) (R : A -> A -> Type ℓR) where
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
  rec isSetB f f~ (squash/ a1 a2 p1 p2 i j) =
    isSetB (g a1) (g a2) (\k -> g (p1 k)) (\k -> g (p2 k)) i j -- (g a1) (g a2) (cong g p1) (cong g p2) i j
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
    isOfHLevel->isOfHLevelDep 2 isSetC (g a1) (g a2) (\k -> g (p1 k)) (\k -> g (p2 k))
      (squash/ a1 a2 p1 p2) i j
    where
    g = elim isSetC f f~

  elimProp : (isPropC : (ar : A / R) -> isProp (C ar)) ->
             (f : (a : A) -> C [ a ]) ->
             (ar : A / R) -> C ar
  elimProp {C = C} isPropC f =
    elim (\ar -> (isProp->isSet (isPropC ar))) f f~
    where
    f~ : (a1 a2 : A) (r : R a1 a2) -> PathP (\i -> C (eq/ a1 a2 r i)) (f a1) (f a2)
    f~ a1 a2 r = isProp->PathP (\i -> isPropC (eq/ a1 a2 r i))

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

  liftContr : (f : (a : A) -> isContr (C [ a ])) ->
              (ar : A / R) -> isContr (C ar)
  liftContr {C = C} f = \ar -> elimProp p (\x -> fst (f x)) ar , p ar _
    where
    p : (ar : A / R) -> isProp (C ar)
    p = elimProp (\_ -> isProp-isProp) (\a -> isContr->isProp (f a))


  liftΠContr :
    {ℓ₁ ℓ₂ : Level}
    {C₁ : A / R -> Type ℓ₁}
    {C₂ : A / R -> Type ℓ₂}
    (f : (a : A) -> (C₁ [ a ]) -> isContr (C₂ [ a ])) ->
    (ar : A / R) -> (C₁ ar) -> isContr (C₂ ar)
  liftΠContr {C₁ = C₁} {C₂ = C₂} f =
    \ar c1 -> g ar c1 , p ar c1 _
    where
    p : (ar : A / R) -> (C₁ ar) -> isProp (C₂ ar)
    p =
      elimProp (\_ -> isPropΠ (\_ -> isProp-isProp))
        (\a c1 -> isContr->isProp (f a c1))

    g : (ar : A / R) -> (C₁ ar) -> (C₂ ar)
    g ar c1 = elimProp (\ar -> isPropΠ (\c1 -> p ar c1)) (\x c1 -> fst (f x c1)) ar c1

  liftContr2 : (f : (a1 a2 : A) -> isContr (C2 [ a1 ] [ a2 ])) ->
               (ar1 ar2 : A / R) -> isContr (C2 ar1 ar2)
  liftContr2 {C2 = C2} f ar1 ar2 =
    liftContr {C = (\ar -> C2 ar ar2)}
      (\a1 -> liftContr {C = (\ar -> C2 [ a1 ] ar)}
                (\a2 -> f a1 a2) ar2)
      ar1

  rec2 : (isSetB : isSet B) (f : A -> A -> B)
         (f~₁ : (a1 a2 a3 : A) (r : R a1 a2) -> (f a1 a3 == f a2 a3)) ->
         (f~₂ : (a1 a2 a3 : A) (r : R a2 a3) -> (f a1 a2 == f a1 a3)) ->
         A / R -> A / R -> B
  rec2 {B = B} isSetB f f~₁ f~₂ =
    rec (isSetΠ (\_ -> isSetB)) g g~
    where
    g : A -> A / R -> B
    g a = rec isSetB (f a) (f~₂ a)

    g~' : (x1 x2 : A) -> (r : R x1 x2) -> (y : A / R) -> g x1 y == g x2 y
    g~' x1 x2 r = elimProp (\i -> isSetB _ _) (\y -> f~₁ x1 x2 y r)

    g~ : (a1 a2 : A) -> (r : R a1 a2) -> g a1 == g a2
    g~ a1 a2 r = funExt (g~' a1 a2 r)


  elim2 : (isSetC2 : (ar1 ar2 : A / R) -> isSet (C2 ar1 ar2))
          (f : (a1 a2 : A) -> C2 [ a1 ] [ a2 ]) ->
          (f~₁ : (a1 a2 a3 : A) (r : R a1 a2) ->
                 PathP (\i -> C2 (eq/ a1 a2 r i) [ a3 ]) (f a1 a3) (f a2 a3))
          (f~₂ : (a1 a2 a3 : A) (r : R a2 a3) ->
                 PathP (\i -> C2 [ a1 ] (eq/ a2 a3 r i)) (f a1 a2) (f a1 a3)) ->
          (ar1 ar2 : A / R) -> C2 ar1 ar2
  elim2 {C2 = C2} isSetC2 f f~₁ f~₂ = elim isSetC' g g~
    where
    g : (a1 : A) -> (ar2 : A / R) -> C2 [ a1 ] ar2
    g a1 = elim (isSetC2 [ a1 ]) (f a1) (f~₂ a1)

    isSetC' : (ar1 : A / R) -> isSet ((ar2 : A / R) -> C2 ar1 ar2)
    isSetC' ar1 = isSetΠ (\ar2 -> isSetC2 ar1 ar2)

    g~' : (a1 a2 : A) (r : R a1 a2) -> (ar3 : A / R) ->
         PathP (\i -> C2 (eq/ a1 a2 r i) ar3) (g a1 ar3) (g a2 ar3)
    g~' a1 a2 r = elimProp hlevel (\a3 -> f~₁ a1 a2 a3 r)
      where
      hlevel : (ar3 : A / R) -> isProp (PathP (\i -> C2 (eq/ a1 a2 r i) ar3) (g a1 ar3) (g a2 ar3))
      hlevel ar3 p1 p2 =
        isOfHLevel->isOfHLevelDep 2 (\x -> isSetC2 x ar3) _ _ _ _ _

    g~ : (a1 a2 : A) (r : R a1 a2) ->
         PathP (\i -> (ar3 : A / R) -> C2 (eq/ a1 a2 r i) ar3) (g a1) (g a2)
    g~ a1 a2 r i ar3 = g~' a1 a2 r ar3 i


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

  pathRecSTRC : (a1 a2 : A) -> Path (A / R) [ a1 ] [ a2 ] ->
                ∥ SymmetricTransitiveReflexiveClosure R a1 a2 ∥
  pathRecSTRC a1 a2 p = transport a1a1=a1a2 ∣ strc-refl ∣
    where
    STRC : A -> A -> Type (ℓ-max ℓR ℓA)
    STRC a1 a2 = ∥ SymmetricTransitiveReflexiveClosure R a1 a2 ∥

    props : (A / R) -> hProp (ℓ-max ℓR ℓA)
    props = rec isSet-hProp prop1 prop1/eq
      where
      prop1 : A -> hProp (ℓ-max ℓR ℓA)
      prop1 a = STRC a1 a , squash
      prop1/eq : (a3 a4 : A) -> (r : R a3 a4) -> prop1 a3 == prop1 a4
      prop1/eq a3 a4 r34 = ΣProp-path isProp-isProp (ua (isoToEquiv i))
        where
        open Iso
        i : Iso (STRC a1 a3) (STRC a1 a4)
        i .fun = ∥-map (\t13 -> strc-trans t13 (strc-rel r34))
        i .inv = ∥-map (\t14 -> strc-trans t14 (strc-sym (strc-rel r34)))
        i .rightInv _ = squash _ _
        i .leftInv _ = squash _ _

    a1a1=a1a2 : STRC a1 a1 == STRC a1 a2
    a1a1=a1a2 = cong fst (cong props p)


  path≃STRC : (a1 a2 : A) -> (Path (A / R) [ a1 ] [ a2 ]) ≃
                             ∥ SymmetricTransitiveReflexiveClosure R a1 a2 ∥
  path≃STRC a1 a2 = isoToEquiv (isProp->iso (pathRecSTRC a1 a2)
                               (\c -> unsquash (squash/ _ _) (∥-map strc->path c))
                               (squash/ _ _) squash)
    where
    strc->path : {a1 a2 : A} -> SymmetricTransitiveReflexiveClosure R a1 a2 -> Path (A / R) [ a1 ] [ a2 ]
    strc->path (strc-rel r) = eq/ _ _ r
    strc->path (strc-refl) = refl
    strc->path (strc-sym c) = sym (strc->path c)
    strc->path (strc-trans c1 c2) = strc->path c1 >=> strc->path c2

module SetQuotientElim {ℓA ℓR : Level} {A : Type ℓA} {R : A -> A -> Type ℓR} where
  open SetQuotientElimᵉ A R public



module _ {ℓA ℓR : Level} {A : Type ℓA} {R : A -> A -> Type ℓR} where
  Discrete-SetQuotient : (isPropValued R) -> (isEquivRel R) -> (Decidable2 R) -> Discrete (A / R)
  Discrete-SetQuotient isProp-R isEquivRel-R decide-R =
    SetQuotientElim.elimProp2 (\_ _ -> isPropDec (squash/ _ _)) f
    where
    f : (a1 a2 : A) -> Dec ([ a1 ] == [ a2 ])
    f a1 a2 = handle (decide-R a1 a2)
      where
      handle : Dec (R a1 a2) -> Dec ([ a1 ] == [ a2 ])
      handle (yes a1~a2) = yes (eq/ a1 a2 a1~a2)
      handle (no ¬a1~a2) = no (¬a1~a2 ∘ SetQuotientElim.pathRec isProp-R isEquivRel-R a1 a2)
