{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic.specialize where

open import base
open import equality-path
open import equivalence
open import isomorphism
open import pointed.spheres
open import pointed.suspension
open import truncation
open import truncation.generic

module _ {ℓ : Level} {A : Type ℓ} where
  Squash≃Squashₙ : Squash A ≃ Squashₙ 1 A
  Squash≃Squashₙ = isoToEquiv (iso fwd bkw fb bf)
    where
    fwd : Squash A -> Squashₙ 1 A
    fwd (∣ x  ∣) = (∣ x ∣)
    fwd (squash a b i) = (sym (spoke f north) >=> (spoke f south)) i
      where
      f : Sⁿ 0 -> Squashₙ 1 A
      f north = fwd a
      f south = fwd b

    bkw : Squashₙ 1 A -> Squash A
    bkw (∣ x ∣) = ∣ x ∣
    bkw (hub f) = bkw (f north)
    bkw (spoke f north i) = bkw (f north)
    bkw (spoke f south i) = squash (bkw (f north)) (bkw (f south)) i

    fb : ∀ x -> fwd (bkw x) == x
    fb x = isOfHLevel-Squashₙ 1 _ _

    bf : ∀ x -> bkw (fwd x) == x
    bf x = squash _ _
