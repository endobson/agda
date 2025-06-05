{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic.truncated where

open import base
open import hlevel.base
open import truncation.generic
open import equivalence
open import isomorphism
open import pointed.spheres
open import pointed.base
open import pointed.suspension

private
  module _ {ℓ : Level} {A : Type ℓ} (hA : isContr A) where
    Squashₙ-truncated⁰-eq : Squashₙ 0 A ≃ A
    Squashₙ-truncated⁰-eq = isoToEquiv (iso for back fb bf)
      where
      for : Squashₙ 0 A -> A
      for _ = fst hA

      back : A -> Squashₙ 0 A
      back _ = lift tt

      fb : ∀ a -> for (back a) == a
      fb a = snd hA a

      bf : ∀ a -> back (for a) == a
      bf _ = refl

  module _ {ℓ : Level} {A : Type ℓ} {n : Nat} (hA : isOfHLevel (suc n) A) where
    Squashₙ-truncated⁺-eq : Squashₙ (suc n) A ≃ A
    Squashₙ-truncated⁺-eq = isoToEquiv (iso for back fb bf)
      where
      for : Squashₙ (suc n) A -> A
      for = ∥ₙ-elim {P = \_ -> A} (\_ -> hA) (\x -> x)

      back : A -> Squashₙ (suc n) A
      back = ∣_∣

      fb : ∀ a -> for (back a) == a
      fb _ = refl

      bf : ∀ a -> back (for a) == a
      bf = ∥ₙ-elim {P = \a -> back (for a) == a}
        (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)
        (\x -> refl)

Squashₙ-truncated-eq : {ℓ : Level} {A : Type ℓ} {n : Nat} (hA : isOfHLevel n A) -> Squashₙ n A ≃ A
Squashₙ-truncated-eq {n = 0} = Squashₙ-truncated⁰-eq
Squashₙ-truncated-eq {n = (suc n)} = Squashₙ-truncated⁺-eq
