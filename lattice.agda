{-# OPTIONS --cubical --safe --exact-split #-}

module lattice where

open import base
open import relation

private
  variable
    ℓ : Level

  Op₂ : Type ℓ -> Type ℓ
  Op₂ D = D -> D -> D

record RawLattice (Domain : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    _≼_ : Rel Domain ℓ
    _∧_ : Op₂ Domain
    _∨_ : Op₂ Domain


module _ {Domain : Type ℓ} where

  record Supremum (_≼_ : Rel Domain ℓ) (_∨_ : Op₂ Domain) : Type ℓ where
    field
      x≼x∨y : ∀ x y -> x ≼ (x ∨ y)
      y≼x∨y : ∀ x y -> y ≼ (x ∨ y)
      ∨-least : ∀ x y z -> x ≼ z -> y ≼ z -> (x ∨ y) ≼ z

  record Infimum (_≼_ : Rel Domain ℓ) (_∧_ : Op₂ Domain) : Type ℓ where
    field
      x∧y≼x : ∀ x y -> (x ∧ y) ≼ x
      x∧y≼y : ∀ x y -> (x ∧ y) ≼ y
      ∧-greatest : ∀ x y z -> z ≼ x -> z ≼ y -> z ≼ (x ∧ y)


  record IsLattice (l : RawLattice Domain) : Type (ℓ-suc ℓ) where
    open RawLattice l public

    field
      partial-order : PartialOrder _≼_
      supremum : Supremum _≼_ _∨_
      infimum : Infimum _≼_ _∧_

    antisym-≼ : Antisymmetric _≼_
    antisym-≼ = proj₂ (proj₂ partial-order)

    refl-≼ : Reflexive _≼_
    refl-≼ = proj₁ (proj₂ partial-order)

    trans-≼ : Transitive _≼_
    trans-≼ = proj₁ partial-order

    open Supremum supremum public
    open Infimum infimum public


  module Lattice (l : RawLattice Domain) {{isLattice : IsLattice l}} where
    open IsLattice isLattice
    private
      D = Domain

    ∧-idempotent : (a : D) -> a ∧ a == a
    ∧-idempotent a = antisym-≼ (x∧y≼x a a) (∧-greatest a a a refl-≼ refl-≼)

    ∨-idempotent : (a : D) -> a ∨ a == a
    ∨-idempotent a = antisym-≼ (∨-least a a a refl-≼ refl-≼) (x≼x∨y a a)
