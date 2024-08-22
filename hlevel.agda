{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel where

open import base
open import cubical
open import discrete
open import equality-path
open import equality.pathp-iso
open import equality.square
open import equivalence
open import functions
open import funext
open import isomorphism
open import relation
open import sigma.base
open import sum
open import univalence

open import hlevel.base public
open import hlevel.decision public
open import hlevel.pi public
open import hlevel.retract public
open import hlevel.sigma public

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A₁ A₂ A₃ : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> B a -> Type ℓ
    D : (a : A) -> (b : B a) -> C a b -> Type ℓ

abstract
  -- h-level for ⊎ types

  isProp⊎ : isProp A₁ -> isProp A₂ -> (A₁ -> ¬ A₂) -> isProp (A₁ ⊎ A₂)
  isProp⊎ ha hb neg (inj-l a1) (inj-l a2) = cong inj-l (ha a1 a2)
  isProp⊎ ha hb neg (inj-l a1) (inj-r b2) = bot-elim (neg a1 b2)
  isProp⊎ ha hb neg (inj-r b1) (inj-l a2) = bot-elim (neg a2 b1)
  isProp⊎ ha hb neg (inj-r b1) (inj-r b2) = cong inj-r (hb b1 b2)

  isSet⊎ : Discrete A₁ -> Discrete A₂ -> isSet (A₁ ⊎ A₂)
  isSet⊎ da db = Discrete->isSet (Discrete⊎ da db)


  -- h-level for function property types

  isPropInjective : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {f : A -> B} ->
                    isSet A -> isProp (Injective f)
  isPropInjective {A = A} {f = f} hA = isPropInj
    where
    isPropInj' : isProp ((a1 a2 : A) -> f a1 == f a2 -> a1 == a2)
    isPropInj' = isPropΠ3 (\ _ _ _ -> hA _ _)

    isPropInj : isProp (Injective f)
    isPropInj g1 g2 i {x} {y} =
      isPropInj' (\a1 a2 p -> g1 {a1} {a2} p) (\a1 a2 p -> g2 {a1} {a2} p) i x y


  -- h-level for equivalences and paths

  isContr->Iso : (isContr A₁) -> (isContr A₂) -> Iso A₁ A₂
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.fun _ = a2
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.inv _ = a1
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.rightInv = f2
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.leftInv = f1

  isContr->Equiv : (isContr A₁) -> (isContr A₂) -> A₁ ≃ A₂
  isContr->Equiv c1 c2 = isoToEquiv (isContr->Iso c1 c2)

  isContr-≃ : (isContr A₁) -> (isContr A₂) -> (isContr (A₁ ≃ A₂))
  isContr-≃ {A₁ = A₁} {A₂ = A₂} c1@(a1 , f1) c2@(a2 , f2) = e1 , f
    where
    e1 : A₁ ≃ A₂
    e1 = isContr->Equiv c1 c2

    f : (e2 : A₁ ≃ A₂) -> e1 == e2
    f e2 = ΣProp-path isProp-isEquiv (funExt (\a1' -> (f2 (e2 .fst a1'))))


  isOfHLevel-≃ : (n : Nat) -> (isOfHLevel n A₁) -> (isOfHLevel n A₂) -> (isOfHLevel n (A₁ ≃ A₂))
  isOfHLevel-≃ 0 = isContr-≃
  isOfHLevel-≃ (suc n) h1 h2 =
    isOfHLevelΣ (suc n) (isOfHLevelΠ (suc n) (\ _ -> h2))
                (\_ -> isProp->isOfHLevelSuc n isProp-isEquiv)

  isProp-≃ : (isProp A₁) -> (isProp A₂) -> (isProp (A₁ ≃ A₂))
  isProp-≃ = isOfHLevel-≃ 1

  isProp-≃-right : (isProp A₂) -> (isProp (A₁ ≃ A₂))
  isProp-≃-right pA2 (f1 , e1) (f2 , e2) = ΣProp-path (isProp-isEquiv) f-path
    where
    f-path : f1 == f2
    f-path = funExt (\x -> pA2 _ _)

  isProp-≃-left : (isProp A₁) -> (isProp (A₁ ≃ A₂))
  isProp-≃-left pA1 e1 e2 = isProp-≃-right (isProp-Retract (eqInv e1) (eqFun e1) (eqSec e1) pA1) e1 e2



  isProp-== : (isProp A₁) -> (isProp A₂) -> isProp (A₁ == A₂)
  isProp-== h1 h2 = isProp-Retract (eqFun univalence) (eqInv univalence) (eqRet univalence)
                                   (isProp-≃ h1 h2)

-- The types of all types that are of a certain hlevel.

hProp : (ℓ : Level) -> Type (ℓ-suc ℓ)
hProp ℓ = Σ (Type ℓ) isProp

hSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
hSet ℓ = Σ (Type ℓ) isSet

abstract
  isSet-hProp : isSet (hProp ℓ)
  isSet-hProp {ℓ} (t1 , h1) (t2 , h2) =
    isProp-Retract (cong fst) (\p -> ΣProp== (\_ -> (isProp-isOfHLevel 1)) p)
                   (section-ΣProp== (\_ -> (isProp-isOfHLevel 1)))
                   (isProp-== h1 h2)


  -- Equivalent types have the same hlevel

  iso-isContr : Iso A₁ A₂ -> isContr A₁ -> isContr A₂
  iso-isContr i = isContr-Retract inv fun rightInv
    where
    open Iso i

  iso-isProp : Iso A₁ A₂ -> isProp A₁ -> isProp A₂
  iso-isProp i = isProp-Retract inv fun rightInv
    where
    open Iso i

  iso-isSet : Iso A₁ A₂ -> isSet A₁ -> isSet A₂
  iso-isSet i = isSet-Retract inv fun rightInv
    where
    open Iso i

  iso-isOfHLevel : Iso A₁ A₂ -> (n : Nat) -> isOfHLevel n A₁ -> isOfHLevel n A₂
  iso-isOfHLevel i n = isOfHLevel-Retract n inv fun rightInv
    where
    open Iso i

  ≃-isContr : A₁ ≃ A₂ -> isContr A₁ -> isContr A₂
  ≃-isContr eq = iso-isContr (equivToIso eq)

  ≃-isProp : A₁ ≃ A₂ -> isProp A₁ -> isProp A₂
  ≃-isProp eq = iso-isProp (equivToIso eq)

  ≃-isSet : A₁ ≃ A₂ -> isSet A₁ -> isSet A₂
  ≃-isSet eq = iso-isSet (equivToIso eq)

  ≃-isOfHLevel : A₁ ≃ A₂ -> (n : Nat) -> isOfHLevel n A₁ -> isOfHLevel n A₂
  ≃-isOfHLevel eq = iso-isOfHLevel (equivToIso eq)

-- h-level for PathP

opaque
  isOfHLevelPathP' : (n : Nat) -> {A : I -> Type ℓ} ->
    ((i : I) -> isOfHLevel (suc n) (A i)) ->
    (x : A i0) (y : A i1) ->
    isOfHLevel n (PathP A x y)
  isOfHLevelPathP' n {A} h x y =
    transport (cong (isOfHLevel n) (sym PathP==transport))
      (isOfHLevelPath' n (h i1) (transport (\k -> A k) x) y)

-- Sets make any square

abstract
  isSet->Square : {ℓ : Level} {A : Type ℓ}
                  {a₀₀ : A} {a₀₁ : A} {a₀₋ : Path A a₀₀ a₀₁}
                  {a₁₀ : A} {a₁₁ : A} {a₁₋ : Path A a₁₀ a₁₁}
                  {a₋₀ : Path A a₀₀ a₁₀}
                  {a₋₁ : Path A a₀₁ a₁₁} -> isSet A -> Square a₀₋ a₁₋ a₋₀ a₋₁
  isSet->Square h = isProp->PathP (\ k -> (h _ _))

  isSet->Squareᵉ : {ℓ : Level} {A : Type ℓ}
                   -> isSet A ->
                   {a₀₀ : A} {a₀₁ : A} (a₀₋ : Path A a₀₀ a₀₁)
                   {a₁₀ : A} {a₁₁ : A} (a₁₋ : Path A a₁₀ a₁₁)
                   (a₋₀ : Path A a₀₀ a₁₀)
                   (a₋₁ : Path A a₀₁ a₁₁) -> Square a₀₋ a₁₋ a₋₀ a₋₁
  isSet->Squareᵉ h _ _ _ _ = isProp->PathP (\ k -> (h _ _))


  isProp->Square : {ℓ : Level} {A : Type ℓ}
                  {a₀₀ : A} {a₀₁ : A} {a₀₋ : Path A a₀₀ a₀₁}
                  {a₁₀ : A} {a₁₁ : A} {a₁₋ : Path A a₁₀ a₁₁}
                  {a₋₀ : Path A a₀₀ a₁₀}
                  {a₋₁ : Path A a₀₁ a₁₁} -> isProp A -> Square a₀₋ a₁₋ a₋₀ a₋₁
  isProp->Square h = isProp->PathP (\ _ -> (isProp->isSet h _ _))

  isSet->SquareP : {ℓ : Level} {A : I -> I -> Type ℓ} ->
                   (∀ i j -> isSet (A i j)) ->
                   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
                   {a₀₋ : PathP (A i0) a₀₀ a₀₁}
                   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
                   {a₁₋ : PathP (A i1) a₁₀ a₁₁}
                   {a₋₀ : PathP (\i -> A i i0) a₀₀ a₁₀}
                   {a₋₁ : PathP (\i -> A i i1) a₀₁ a₁₁} ->
                   SquareP A a₀₋ a₁₋ a₋₀ a₋₁
  isSet->SquareP h = isProp->PathP (\i -> isOfHLevelPathP' 1 (h i) _ _)

  isSet->SquarePᵉ : {ℓ : Level} {A : I -> I -> Type ℓ} ->
                    (∀ i j -> isSet (A i j)) ->
                    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
                    (a₀₋ : PathP (A i0) a₀₀ a₀₁)
                    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
                    (a₁₋ : PathP (A i1) a₁₀ a₁₁)
                    (a₋₀ : PathP (\i -> A i i0) a₀₀ a₁₀)
                    (a₋₁ : PathP (\i -> A i i1) a₀₁ a₁₁) ->
                    SquareP A a₀₋ a₁₋ a₋₀ a₋₁
  isSet->SquarePᵉ h _ _ _ _ = isSet->SquareP h

-- Acc/WellFounded

isProp-Acc : (R : Rel A ℓ) -> (a : A) -> isProp (Acc R a)
isProp-Acc R a (acc f) (acc g) i =
  acc (\y yRa -> isProp-Acc R y (f y yRa) (g y yRa) i)

isProp-WellFounded : (R : Rel A ℓ) -> isProp (WellFounded R)
isProp-WellFounded R = isPropΠ (\a -> isProp-Acc R a)

-- Lift

isProp-Lift : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> isProp A -> isProp (Lift ℓ₂ A)
isProp-Lift = ≃-isProp (equiv⁻¹ (liftEquiv _ _))

isSet-Lift : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> isSet A -> isSet (Lift ℓ₂ A)
isSet-Lift = ≃-isSet (equiv⁻¹ (liftEquiv _ _))
