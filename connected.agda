{-# OPTIONS --cubical --safe --exact-split #-}

module connected where

open import base
open import hlevel
open import isomorphism
open import equality-path
open import equivalence.base
open import truncation.generic
open import truncation.generic.path
open import pointed.base
open import univalence
open import pointed.suspension

-- TODO fix this to match literature
-- Currently this is two higher than standard
-- 0 corresponds to always true
-- 1 corresponds to inhabited spaces
-- 2 corresponds to simply connected

isConnectedₙ : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ
isConnectedₙ n A = isContr (Squashₙ n A)

isConnectedMapₙ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                  Nat -> (A -> B) -> Type (ℓ-max ℓA ℓB)
isConnectedMapₙ n f = ∀ b -> isConnectedₙ n (fiber f b)

isProp-isConnectedₙ : {ℓ : Level} (n : Nat) (A : Type ℓ) -> isProp (isConnectedₙ n A)
isProp-isConnectedₙ n A = isProp-isContr

isProp-isConnectedMapₙ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
                         (n :  Nat) -> (f : (A -> B)) -> isProp (isConnectedMapₙ n f)
isProp-isConnectedMapₙ n f = isPropΠ (\_ -> isProp-isContr)


private
  module _ {ℓA : Level} (A∙@(A , ★A) : Type∙ ℓA) where

    isConnectedₙ∙-eq-0 : (isConnectedₙ (suc zero) A) ≃ isConnectedMapₙ zero (\ (_ : Top) -> ★A)
    isConnectedₙ∙-eq-0 =
      isoToEquiv (isProp->iso f b (isProp-isConnectedₙ 1 A) (isProp-isConnectedMapₙ 0 (\(_ : Top) -> ★A)))
      where
      f : (isConnectedₙ (suc zero) A) -> isConnectedMapₙ zero (\ (_ : Top) -> ★A)
      f c = ans
        where
        check : isContr (Squashₙ (suc zero) A)
        check = c
        ans : ∀ a -> isContr (Squashₙ zero (fiber (\(_ : Top) -> ★A) a))
        ans _ = isContr-Lift isContrTop

      b : isConnectedMapₙ zero (\ (_ : Top) -> ★A) -> isConnectedₙ 1 A
      b _ = ∣ ★A ∣ , isOfHLevel-Squashₙ 1 _


module _ {ℓA : Level} (n : Nat) (A∙@(A , ★A) : Type∙ ℓA) where

  isConnectedₙ∙-path : (isConnectedₙ (suc n) A) == isConnectedMapₙ n (\ (_ : Top) -> ★A)
  isConnectedₙ∙-path = sym path₂
    where
    fiber-iso : ∀ a -> Iso (fiber (\(_ : Top) -> ★A) a) (★A == a)
    fiber-iso a = iso f b (\_ -> refl) (\_ -> refl)
      where
      f : (fiber (\(_ : Top) -> ★A) a) -> (★A == a)
      f (tt , p) = p

      b : (★A == a) -> (fiber (\(_ : Top) -> ★A) a)
      b p = (tt , p)

    connected-iso :
      Iso (isConnectedₙ (suc n) A)
          (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a))
    connected-iso =
      isProp->iso f b (isProp-isConnectedₙ _ _) (isPropΠ (\_ -> isProp-isContr))
      where
      f : (isConnectedₙ (suc n) A) ->
          (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a))
      f c a = isContr->isContrPath c (squashₙ (suc n) ★A) (squashₙ (suc n) a)
      b : (∀ a -> isContr (squashₙ (suc n) ★A == squashₙ (suc n) a)) ->
          (isConnectedₙ (suc n) A)
      b c =
        squashₙ (suc n) ★A ,
        ∥ₙ-elim (\a -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)
                (\a -> (fst (c a)))

    path : ∀ a -> (Squashₙ n (fiber (\(_ : Top) -> ★A) a)) ==
                  (squashₙ (suc n) ★A == squashₙ (suc n) a)
    path a = cong (Squashₙ n) (isoToPath (fiber-iso a)) >=>
             ua (squashed-path-eq n ★A a)

    path₂ : isConnectedMapₙ n (\(_ : Top) -> ★A) ==
            isConnectedₙ (suc n) A
    path₂ = (\i -> ∀ a -> isContr (path a i)) >=>
            (sym (isoToPath connected-iso))


-- module _ {ℓA : Level} (n : Nat) (A∙@(A , ★A) : Type∙ ℓA) where
--   isConnected
