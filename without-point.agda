{-# OPTIONS --cubical --safe --exact-split #-}

module without-point where

open import base
open import discrete
open import equality
open import equivalence.base
open import functions
open import hlevel
open import maybe
open import relation
open import sigma
open import sigma.base
open import truncation

record WithoutPoint {ℓ : Level} (A : Type ℓ) (point : A) : Type ℓ where
  constructor _,_
  field
    value : A
    ¬point : value != point

WithoutPoint-path : {ℓ : Level} {A : Type ℓ} {a : A} {p1 p2 : WithoutPoint A a} ->
  (WithoutPoint.value p1 == WithoutPoint.value p2) -> p1 == p2
WithoutPoint-path {p1 = p1} {p2 = p2} path i =
  (path i) ,
  (isProp->PathPᵉ (\i -> isProp¬ᵉ (path i == _))
    (WithoutPoint.¬point p1)
    (WithoutPoint.¬point p2) i)

module _ {ℓ : Level} {A : Type ℓ} {{D : Discrete' A}} where
  opaque
    instance
      Discrete'-WithoutPoint : {a : A} -> Discrete' (WithoutPoint A a)
      Discrete'-WithoutPoint .Discrete'.f (a2 , _) (a3 , _) with decide-= a2 a3
      ... | (yes a2=a3) = yes (WithoutPoint-path a2=a3)
      ... | (no a2!=a3) = no (a2!=a3 ∘ cong WithoutPoint.value)

MaybeWithoutPoint-eq : {ℓ : Level} (A : Type ℓ) {{D : Discrete' A}} (a : A) ->
                       Maybe (WithoutPoint A a) ≃ A
MaybeWithoutPoint-eq A a =
  f , record { equiv-proof = \a2 -> fibf a2 , isProp-fibf a2 _ }
  where
  f : Maybe (WithoutPoint A a) -> A
  f (nothing) = a
  f (just (a2 , _)) = a2

  opaque
    isProp-fibf : (a2 : A) -> isProp (fiber f a2)
    isProp-fibf a2 (nothing , p1) (nothing , p2) =
      ΣProp-path (Discrete->isSet decide-= _ _) refl
    isProp-fibf a2 (nothing , p1) (just (a3 , ¬p3) , p2) =
      bot-elim (¬p3 (p2 >=> sym p1))
    isProp-fibf a2 (just (a3 , ¬p3) , p1) (nothing , p2) =
      bot-elim (¬p3 (p1 >=> sym p2))
    isProp-fibf a2 (just (a3 , ¬p3) , p1) (just (a4 , ¬p4) , p2) =
      ΣProp-path (Discrete->isSet decide-= _ _)
        (cong just (WithoutPoint-path (p1 >=> sym p2)))

    fibf : (a2 : A) -> fiber f a2
    fibf a2 = (g a2 (decide-= a a2))
      where
      g : (a2 : A) -> Dec (a == a2) -> fiber f a2
      g a2 (yes p) = (nothing , p)
      g a2 (no ¬p) = just (a2 , ¬p ∘ sym) , refl
