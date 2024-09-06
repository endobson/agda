{-# OPTIONS --cubical --safe --exact-split #-}

module semigroup where

open import base
open import equality
open import hlevel.base

record SemigroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 6 _∙_

  field
    _∙_ : Domain -> Domain -> Domain
    ∙-assoc : {m n o : Domain} -> (m ∙ n) ∙ o == m ∙ (n ∙ o)
    isSet-Domain : isSet Domain

  ∙-right : {m n o : Domain} -> (n == o) -> m ∙ n == m ∙ o
  ∙-right {m} p i = m ∙ p i

  ∙-left : {m n o : Domain} -> (n == o) -> n ∙ m == o ∙ m
  ∙-left {m} p i = p i ∙ m

Semigroup : (ℓ : Level) -> Type (ℓ-suc ℓ)
Semigroup ℓ = Σ[ D ∈ Type ℓ ] (SemigroupStr D)

record CommutativeSemigroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 6 _∙_

  field
    _∙_ : Domain -> Domain -> Domain
    ∙-assoc : {m n o : Domain} -> (m ∙ n) ∙ o == m ∙ (n ∙ o)
    ∙-commute : {m n : Domain} -> m ∙ n == n ∙ m
    isSet-Domain : isSet Domain

  ∙-right : {m n o : Domain} -> (n == o) -> m ∙ n == m ∙ o
  ∙-right {m} p i = m ∙ p i

  ∙-left : {m n o : Domain} -> (n == o) -> n ∙ m == o ∙ m
  ∙-left {m} p i = p i ∙ m

CommutativeSemigroup : (ℓ : Level) -> Type (ℓ-suc ℓ)
CommutativeSemigroup ℓ = Σ[ D ∈ Type ℓ ] (CommutativeSemigroupStr D)
