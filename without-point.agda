{-# OPTIONS --cubical --safe --exact-split #-}

module without-point where

open import base
open import equality
open import equivalence.base
open import functions
open import hlevel
open import maybe
open import relation
open import sigma
open import sigma.base
open import truncation

WithoutPoint : {ℓ : Level} (A : Type ℓ) -> (a : A) -> Type ℓ
WithoutPoint A a = Σ[ a2 ∈ A ] (a2 != a)

abstract
  Discrete-WithoutPoint :
    {ℓ : Level} {A : Type ℓ} -> (Discrete A) -> (a : A) -> Discrete (WithoutPoint A a)
  Discrete-WithoutPoint discA _ (a2 , _) (a3 , _) with discA a2 a3
  ... | (yes a2=a3) = yes (ΣProp-path (isProp¬ _) a2=a3)
  ... | (no a2!=a3) = no (a2!=a3 ∘ cong fst)

MaybeWithoutPoint-eq : {ℓ : Level} (A : Type ℓ) -> (Discrete A) -> (a : A) ->
                       Maybe (WithoutPoint A a) ≃ A
MaybeWithoutPoint-eq A discA a =
  f , record { equiv-proof = \a2 -> fibf a2 , isProp-fibf a2 _ }
  where
  f : Maybe (WithoutPoint A a) -> A
  f (nothing) = a
  f (just (a2 , _)) = a2

  abstract
    isProp-fibf : (a2 : A) -> isProp (fiber f a2)
    isProp-fibf a2 (nothing , p1) (nothing , p2) =
      ΣProp-path (Discrete->isSet discA _ _) refl
    isProp-fibf a2 (nothing , p1) (just (a3 , ¬p3) , p2) =
      bot-elim (¬p3 (p2 >=> sym p1))
    isProp-fibf a2 (just (a3 , ¬p3) , p1) (nothing , p2) =
      bot-elim (¬p3 (p1 >=> sym p2))
    isProp-fibf a2 (just (a3 , ¬p3) , p1) (just (a4 , ¬p4) , p2) =
      ΣProp-path (Discrete->isSet discA _ _)
        (cong just (ΣProp-path (isProp¬ _) (p1 >=> sym p2)))

    fibf : (a2 : A) -> fiber f a2
    fibf a2 = (g a2 (discA a a2))
      where
      g : (a2 : A) -> Dec (a == a2) -> fiber f a2
      g a2 (yes p) = (nothing , p)
      g a2 (no ¬p) = just (a2 , ¬p ∘ sym) , refl
