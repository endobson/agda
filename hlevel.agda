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
open import univalence

open import hlevel.base public
open import hlevel.decision public
open import hlevel.equivalence public
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
  -- h-level for Dec

  isProp-Dec : isProp A -> isProp (Dec A)
  isProp-Dec hA (yes a1) (yes a2) = cong yes (hA a1 a2)
  isProp-Dec hA (yes a)  (no ¬a) = bot-elim (¬a a)
  isProp-Dec hA (no ¬a)  (yes a) = bot-elim (¬a a)
  isProp-Dec hA (no ¬a1) (no ¬a2) = cong no (isProp¬ ¬a1 ¬a2)

  -- h-level for function property types

  isProp-isInjective : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {f : A -> B} ->
                    isSet A -> isProp (isInjective f)
  isProp-isInjective {A = A} {f = f} hA = isPropInj
    where
    isPropInj' : isProp ((a1 a2 : A) -> f a1 == f a2 -> a1 == a2)
    isPropInj' = isPropΠ3 (\ _ _ _ -> hA _ _)

    isPropInj : isProp (isInjective f)
    isPropInj g1 g2 i {x} {y} =
      isPropInj' (\a1 a2 p -> g1 {a1} {a2} p) (\a1 a2 p -> g2 {a1} {a2} p) i x y





  isProp-== : (isProp A₁) -> (isProp A₂) -> isProp (A₁ == A₂)
  isProp-== h1 h2 = isProp-Retract (eqFun univalence) (eqInv univalence) (eqRet univalence)
                                   (isProp-≃ h1 h2)

abstract
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

isContr-Lift : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> isContr A -> isContr (Lift ℓ₂ A)
isContr-Lift = ≃-isContr (equiv⁻¹ (liftEquiv _ _))

isProp-Lift : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> isProp A -> isProp (Lift ℓ₂ A)
isProp-Lift = ≃-isProp (equiv⁻¹ (liftEquiv _ _))

isSet-Lift : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> isSet A -> isSet (Lift ℓ₂ A)
isSet-Lift = ≃-isSet (equiv⁻¹ (liftEquiv _ _))
