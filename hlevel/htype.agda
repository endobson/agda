{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.htype where

open import base
open import cubical
open import hlevel.base
open import hlevel
open import equivalence
open import equality-path
open import univalence
open import isomorphism
open import sigma.base


-- The types of all types that are of a certain hlevel.

hType : Nat -> (ℓ : Level) -> Type (ℓ-suc ℓ)
hType n ℓ = Σ (Type ℓ) (isOfHLevel n)

hProp : (ℓ : Level) -> Type (ℓ-suc ℓ)
hProp = hType 1

hSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
hSet = hType 2

opaque
  isOfHLevel-hType : {ℓ : Level} -> (n : Nat) -> isOfHLevel (suc n) (hType n ℓ)
  isOfHLevel-hType zero (A , (cA , fA)) (B , (cB , fB)) =
    ΣProp-path isProp-isContr (isoToPath (iso (\_ -> cB) (\_ -> cA) fB fA))
  isOfHLevel-hType {ℓ} (suc n) A'@(A , hA) B'@(B , hB) =
    ≃-isOfHLevel (equiv⁻¹ (T₁≃T₂ >eq> univalence)) (suc n) (isOfHLevel-≃ (suc n) hA hB)
    where
    T₁ : Type (ℓ-suc ℓ)
    T₁ = A' == B'
    T₂ : Type (ℓ-suc ℓ)
    T₂ = A == B

    T₁≃T₂ : T₁ ≃ T₂
    T₁≃T₂ = isoToEquiv (iso f b (\_ -> refl) bf)
      where
      f : T₁ -> T₂
      f p = cong fst p
      b : T₂ -> T₁
      b p = Σ-path p (isProp->PathP (\_ -> isProp-isOfHLevel (suc n)))
      bf : ∀ x -> b (f x) == x
      bf p i j = _ , ans i j
        where
        ans : Path (PathP (\i -> isOfHLevel (suc n) (fst (p i))) hA hB) (cong snd (b (f p))) (cong snd p)
        ans =
          transport (\j -> isProp (PathP (\i -> isOfHLevel (suc n) (fst (p (i ∧ j)))) hA (snd (p j))))
            (isProp->isSet (isProp-isOfHLevel (suc n)) _ _) _ _

isSet-hProp : {ℓ : Level} -> isSet (hProp ℓ)
isSet-hProp = isOfHLevel-hType 1
