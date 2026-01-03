{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.rational where

open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality-path
open import int.base
open import int.order
open import int.sign
open import nat
open import rational
open import ring
open import ring.implementations.int
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import semiring.natural-reciprocal
open import set-quotient
open import truncation

open rational public using
  ( Ring-ℚ
  ; Semiring-ℚ
  ; AdditiveCommMonoid-ℚ
  )

Semiringʰ-ℤ->ℚ : Semiringʰ ℤ->ℚ
Semiringʰ-ℤ->ℚ = record
  { +ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = ℤ->ℚ-preserves-+
    }
  ; *ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = ℤ->ℚ-preserves-*
    }
  }

Ringʰ-ℤ->ℚ : Ringʰ ℤ->ℚ
Ringʰ-ℤ->ℚ = record
  { preserves-0# = refl
  ; preserves-1# = refl
  ; preserves-+ = ℤ->ℚ-preserves-+
  ; preserves-* = ℤ->ℚ-preserves-*
  ; preserves-minus = ℤ->ℚ-preserves-minus
  }

Semiringʰ-ℕ->ℚ : Semiringʰ ℕ->ℚ
Semiringʰ-ℕ->ℚ = Semiringʰ-∘ Semiringʰ-ℤ->ℚ Semiringʰ-ℕ->ℤ

instance
  ℕ->Semiring-ℚ : ℕ->Semiring-Op ℚ
  ℕ->Semiring-ℚ = ℕ->SemiringStr-cons Semiringʰ-ℕ->ℚ

private
  opaque
    unfolding _r*_

    ℕ-1/ℕ-path-ℚ : (n : Nat⁺) -> (ℕ->ℚ ⟨ n ⟩) * (ℚ'->ℚ (1/ℕ' n)) == 1#
    ℕ-1/ℕ-path-ℚ n = eq/ _ _ (ℕ-1/ℕ-r~ n)

instance
  1/ℕ-Op-ℚ : 1/ℕ-Op ℚ
  1/ℕ-Op-ℚ = record
    { f = \n -> ℚ'->ℚ (1/ℕ' n)
    ; path = ℕ-1/ℕ-path-ℚ
    }

-- TODO find better home for this
opaque
  ℚ->split-ℤ/ℕ : (q : ℚ) -> ∃[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d)
  ℚ->split-ℤ/ℕ q = ∥-map handle (ℚ->split-ℤℕ⁺ q)
    where
    handle :
        Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (ℤ->ℚ n == q * ℕ->ℚ ⟨ d ⟩) ->
        Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d)
    handle (n , d , p) = n , d , p'
      where
      module _ where
        p' : (q == ℤ->ℚ n * 1/ℕ d)
        p' = sym (cong (_* 1/ℕ d) p >=>
                  *-assoc >=>
                  *-right (*-commute >=> 1/ℕ-ℕ-path d) >=>
                  *-right-one)
