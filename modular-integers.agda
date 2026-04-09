{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers where

open import additive-group
open import additive-group.instances.int
open import base
open import div
open import hlevel.base
open import int.base
open import int.sign
open import nat
open import ring
open import semiring
open import ring.implementations.int
open import equality-path
open import relation
open import set-quotient

ℤ/nℤ~ : ℕ -> Rel ℤ ℓ-zero
ℤ/nℤ~ n x y = (nonneg n) div (diff x y)

ℤ/nℤ : ℕ -> Type₀
ℤ/nℤ n = ℤ / (ℤ/nℤ~ n)

isSet-ℤ/nℤ : {n : Nat} -> isSet (ℤ/nℤ n)
isSet-ℤ/nℤ = squash/

opaque
  isEquivRel-ℤ/nℤ~ : {n : Nat} -> isEquivRel (ℤ/nℤ~ n)
  isEquivRel-ℤ/nℤ~ {n} = equivRel refl-~ sym-~ trans-~
    where
    sym-~ : {x y : ℤ} -> ℤ/nℤ~ n x y -> ℤ/nℤ~ n y x
    sym-~ (i , p) = (- i , minus-extract-left >=> cong -_ p >=> sym diff-anticommute)

    refl-~ : Reflexive (ℤ/nℤ~ n)
    refl-~ {x} = 0# , *-left-zero >=> sym +-inverse

    trans-~ : Transitive (ℤ/nℤ~ n)
    trans-~ (d₁ , p₁) (d₂ , p₂) =
      d₁ + d₂ , *-distrib-+-right >=> +-cong p₁ p₂ >=> diff-trans

  isProp-ℤ/nℤ~ : ((n , _) : Nat⁺) -> isPropValued (ℤ/nℤ~ n)
  isProp-ℤ/nℤ~ (_ , pos-n) a b n%ab₁ n%ab₂ =
    isPropDiv₁ (Pos->NonZero (Pos'->Pos pos-n)) n%ab₁ n%ab₂
