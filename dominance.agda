{-# OPTIONS --cubical --safe --exact-split #-}

module dominance where

open import base
open import equality
open import equivalence
open import hlevel
open import isomorphism
open import relation

record isDominance {ℓ : Level} (D : Type ℓ -> Type ℓ) : Type (ℓ-suc ℓ) where
  field
    isProp-D : ∀ X -> isProp (D X)
    isProp-X : ∀ X -> D X -> isProp X
    D-Top : D (Lift ℓ Top)
    closed : ∀ X (Y : X -> Type ℓ) -> D X -> (∀ x -> D (Y x)) -> D (Σ X Y)

Dominance : (ℓ : Level) -> Type (ℓ-suc ℓ)
Dominance ℓ = Σ (Type ℓ -> Type ℓ) isDominance

module Dominance {ℓ : Level} (D : Dominance ℓ) where
  private
    D' : Type ℓ -> Type ℓ
    D' = fst D
  isProp-D : ∀ X -> isProp (D' X)
  isProp-D = isDominance.isProp-D (snd D)
  isProp-X : ∀ X -> D' X -> isProp X
  isProp-X = isDominance.isProp-X (snd D)
  D-Top : D' (Lift ℓ Top)
  D-Top = isDominance.D-Top (snd D)
  closed : ∀ X (Y : X -> Type ℓ) -> D' X -> (∀ x -> D' (Y x)) -> D' (Σ X Y)
  closed = isDominance.closed (snd D)

Dominance-isContr : {ℓ : Level} -> Dominance ℓ
Dominance-isContr = isContr , record
  { isProp-D = \_ -> isProp-isContr
  ; isProp-X = \_ c -> isContr->isProp c
  ; D-Top = lift tt , \_ -> refl
  ; closed = \_ _ -> isContrΣ
  }

Dominance-isProp : {ℓ : Level} -> Dominance ℓ
Dominance-isProp = isProp , record
  { isProp-D = \_ -> isProp-isProp
  ; isProp-X = \_ c -> c
  ; D-Top = ≃-isProp (equiv⁻¹ (liftEquiv _ Top)) isPropTop
  ; closed = \_ _ -> isPropΣ
  }

Dominance-Dec : {ℓ : Level} -> Dominance ℓ
Dominance-Dec {ℓ} = D , record
  { isProp-D = isProp-D
  ; isProp-X = isProp-X
  ; D-Top = D-Top
  ; closed = closed
  }
  where
  D : Type ℓ -> Type ℓ
  D X = isProp X × Dec X

  isProp-D : ∀ X -> isProp (D X)
  isProp-D _ = isPropΣ isProp-isProp isPropDec

  isProp-X : ∀ X -> D X -> isProp X
  isProp-X _ = proj₁

  D-Top : D (Lift ℓ Top)
  D-Top = ≃-isProp (equiv⁻¹ (liftEquiv _ Top)) isPropTop , yes (lift tt)

  closed : ∀ X (Y : X -> Type ℓ) -> D X -> (∀ x -> D (Y x)) -> D (Σ X Y)
  closed X Y DX DY = isPropΣ (proj₁ DX) (\x -> proj₁ (DY x)) ,
                     (handle DX)
    where
    handle : D X -> Dec (Σ X Y)
    handle (isProp-X , yes x) with (DY x)
    ... | (_ , yes y) = yes (x , y)
    ... | (_ , no ¬y) = no \{ (x2 , y) -> ¬y (subst Y (isProp-X x2 x) y) }
    handle (_ , no ¬x) = no \{ (x , _) -> ¬x x }
