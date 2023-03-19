{-# OPTIONS --cubical --safe --exact-split #-}

module ring.solver-equations where

open import base
open import equality
open import additive-group
open import semiring
open import solver
open import ring
open import nat
open import truncation
open import ring.initial-integers
open import semiring.initial
open import funext
open import int
open import ring.implementations.int


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}} {{S : Semiring ACM}} where

  private
    R : Ring S AG
    R = record {}
    module RSolver = RingSolver R
    instance
      IACM = ACM
      IR = R

    diff' : {n : Nat} -> RingSyntax n -> RingSyntax n -> RingSyntax n
    diff' a b = (b ⊕ (⊖ a))

    ℕ->D' : ℕ -> D
    ℕ->D' n = (∃!-val ∃!ℤ->Ring (int n))

    ℕ->D'ʰ : Semiringʰᵉ _ _ ℕ->D'
    ℕ->D'ʰ = Semiringʰ-∘ (Ringʰ.semiringʰ (∃!-prop ∃!ℤ->Ring)) Semiringʰ-ℕ->ℤ

    ℕ->D : ℕ -> D
    ℕ->D = ℕ->Semiring

    ℕ->D-path : ℕ->D == ℕ->D'
    ℕ->D-path = ∃!-unique ∃!ℕ->Semiring ℕ->D' ℕ->D'ʰ

    _^ℕ_ : D -> ℕ -> D
    x ^ℕ zero = ℕ->D' 1
    x ^ℕ (suc n) =  x * (x ^ℕ n)

    _^ℕ'_ : {n : ℕ} -> RingSyntax n -> ℕ -> RingSyntax n
    x ^ℕ' zero = (© 1#)
    x ^ℕ' (suc n) =  x ⊗ (x ^ℕ' n)

    _^ℕᵉ_ : D -> ℕ -> D
    x ^ℕᵉ zero = 1#
    x ^ℕᵉ (suc n) =  x * (x ^ℕᵉ n)

    ^ℕ-path : (x : D) (n : ℕ) -> x ^ℕᵉ n == x ^ℕ n
    ^ℕ-path x zero = sym (Semiringʰ.preserves-1# ℕ->D'ʰ)
    ^ℕ-path x (suc n) i = x * (^ℕ-path x n i)


  abstract
    diff-*-expand : {a b c d : D} ->
      diff (a * b) (c * d) ==
      (diff (a * b) (c * b) + diff (a * b) (a * d)) + (diff a c) * (diff b d)
    diff-*-expand = RSolver.solve 4 (\a b c d ->
      diff' (a ⊗ b) (c ⊗ d) ,
      (diff' (a ⊗ b) (c ⊗ b) ⊕ diff' (a ⊗ b) (a ⊗ d)) ⊕ (diff' a c) ⊗ (diff' b d))
      refl _ _ _ _

    private
      [1-x]^3-expand' : {x : D} ->
        (ℕ->D' 1 + (- x)) ^ℕ 3 ==
        (ℕ->D' 1 + (- ((ℕ->D' 2) * x))) +
        (ℕ->D' 1 + (- ((ℕ->D' 3) * x)) + (x * x)) * (- x)
      [1-x]^3-expand' {x} = RSolver.solve 1 (\x ->
        ((© (int 1)) ⊕ (⊖ x)) ^ℕ' 3 ,
        ((© (int 1)) ⊕ (⊖ ((© (int 2)) ⊗ x))) ⊕
        ((© (int 1)) ⊕ (⊖ ((© (int 3)) ⊗ x)) ⊕ (x ⊗ x)) ⊗ (⊖ x))
        refl x

    [1-x]^3-expand : (x : D) ->
      (ℕ->D 1 + (- x)) ^ℕᵉ 3 ==
      (ℕ->D 1 + (- ((ℕ->D 2) * x))) +
      (ℕ->D 1 + (- ((ℕ->D 3) * x)) + (x * x)) * (- x)
    [1-x]^3-expand x =
      subst2 (\ℕ->D x^3 -> x^3 (ℕ->D 1 + (- x)) ==
                           (ℕ->D 1 + (- ((ℕ->D 2) * x))) +
                           (ℕ->D 1 + (- ((ℕ->D 3) * x)) + (x * x)) * (- x))
            (sym ℕ->D-path) (sym (funExt (\x -> (^ℕ-path x 3)))) [1-x]^3-expand'
