{-# OPTIONS --cubical --safe --exact-split #-}

module connected where

open import base
open import equality-path
open import equivalence.base
open import hlevel
open import hlevel.base
open import isomorphism
open import pointed.base
open import truncation.generic
open import truncation.generic.path
open import univalence


-- Base defintion of Connectedness.
-- Indexed starting at -2.
isConnectedₙ₋₂ : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ
isConnectedₙ₋₂ n A = isContr (Squashₙ n A)

isProp-isConnectedₙ₋₂ : {ℓ : Level} (n : Nat) (A : Type ℓ) -> isProp (isConnectedₙ₋₂ n A)
isProp-isConnectedₙ₋₂ n A = isProp-isContr

-- Common cases of isConnected
isConnected₋₂ : {ℓ : Level} -> Type ℓ -> Type ℓ
isConnected₋₂ = isConnectedₙ₋₂ 0

isConnected₋₁ : {ℓ : Level} -> Type ℓ -> Type ℓ
isConnected₋₁ = isConnectedₙ₋₂ 1

isConnected : {ℓ : Level} -> Type ℓ -> Type ℓ
isConnected = isConnectedₙ₋₂ 2

isSimplyConnected : {ℓ : Level} -> Type ℓ -> Type ℓ
isSimplyConnected = isConnectedₙ₋₂ 3


-- Generic isConnected
isConnectedₙ : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ
isConnectedₙ n = isConnectedₙ₋₂ (suc (suc n))

isProp-isConnectedₙ : {ℓ : Level} (n : Nat) (A : Type ℓ) -> isProp (isConnectedₙ n A)
isProp-isConnectedₙ n = isProp-isConnectedₙ₋₂ (suc (suc n))

-- Connected maps
isConnectedMapₙ₋₂ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                     Nat -> (A -> B) -> Type (ℓ-max ℓA ℓB)
isConnectedMapₙ₋₂ n f = ∀ b -> isConnectedₙ₋₂ n (fiber f b)
isConnectedMapₙ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                  Nat -> (A -> B) -> Type (ℓ-max ℓA ℓB)
isConnectedMapₙ n = isConnectedMapₙ₋₂ (suc (suc n))

isProp-isConnectedMapₙ₋₂ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                           (n :  Nat) -> (f : (A -> B)) -> isProp (isConnectedMapₙ₋₂ n f)
isProp-isConnectedMapₙ₋₂ n f = isPropΠ (\_ -> isProp-isContr)
isProp-isConnectedMapₙ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                         (n :  Nat) -> (f : (A -> B)) -> isProp (isConnectedMapₙ n f)
isProp-isConnectedMapₙ n = isProp-isConnectedMapₙ₋₂ (suc (suc n))


private
  module _ {ℓA : Level} (A∙@(A , ★A) : Type∙ ℓA) where

    isConnectedₙ∙-eq-0 : (isConnected₋₁ A) ≃ isConnectedMapₙ₋₂ zero (\ (_ : Top) -> ★A)
    isConnectedₙ∙-eq-0 =
      isoToEquiv (isProp->iso f b (isProp-isConnectedₙ₋₂ 1 A) (isProp-isConnectedMapₙ₋₂ 0 (\(_ : Top) -> ★A)))
      where
      f : (isConnected₋₁ A) -> isConnectedMapₙ₋₂ zero (\ (_ : Top) -> ★A)
      f c = ans
        where
        check : isContr (Squashₙ (suc zero) A)
        check = c
        ans : ∀ a -> isContr (Squashₙ zero (fiber (\(_ : Top) -> ★A) a))
        ans _ = isContr-Lift isContrTop

      b : isConnectedMapₙ₋₂ zero (\ (_ : Top) -> ★A) -> isConnected₋₁ A
      b _ = ∣ ★A ∣ , isOfHLevel-Squashₙ 1 _


module _ {ℓA : Level} (n : Nat) (A∙@(A , ★A) : Type∙ ℓA) where
  opaque
    isConnectedₙ₋₂∙-path : (isConnectedₙ₋₂ (suc n) A) == isConnectedMapₙ₋₂ n (\ (_ : Top) -> ★A)
    isConnectedₙ₋₂∙-path = sym path₂
      where
      fiber-iso : ∀ a -> Iso (fiber (\(_ : Top) -> ★A) a) (★A == a)
      fiber-iso a = iso f b (\_ -> refl) (\_ -> refl)
        where
        f : (fiber (\(_ : Top) -> ★A) a) -> (★A == a)
        f (tt , p) = p

        b : (★A == a) -> (fiber (\(_ : Top) -> ★A) a)
        b p = (tt , p)

      connected-iso :
        Iso (isConnectedₙ₋₂ (suc n) A)
            (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a))
      connected-iso =
        isProp->iso f b (isProp-isConnectedₙ₋₂ _ _) (isPropΠ (\_ -> isProp-isContr))
        where
        f : (isConnectedₙ₋₂ (suc n) A) ->
            (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a))
        f c a = isContr->isContrPath c (squashₙ (suc n) ★A) (squashₙ (suc n) a)
        b : (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a)) ->
            (isConnectedₙ₋₂ (suc n) A)
        b c =
          squashₙ (suc n) ★A ,
          ∥ₙ-elim (\a -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)
                  (\a -> (fst (c a)))

      path : ∀ a -> (Squashₙ n (fiber (\(_ : Top) -> ★A) a)) ==
                    (squashₙ (suc n) ★A == squashₙ (suc n) a)
      path a = cong (Squashₙ n) (isoToPath (fiber-iso a)) >=>
               ua (squashed-path-eq n ★A a)

      path₂ : isConnectedMapₙ₋₂ n (\(_ : Top) -> ★A) ==
              isConnectedₙ₋₂ (suc n) A
      path₂ = (\i -> ∀ a -> isContr (path a i)) >=>
              (sym (isoToPath connected-iso))
