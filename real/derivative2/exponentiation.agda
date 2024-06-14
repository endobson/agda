{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.exponentiation where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import nat
open import heyting-field.instances.real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.rational
open import real.derivative2
open import real.derivative2.constant
open import real.derivative2.identity
open import real.derivative2.multiplication
open import real.sequence.harmonic
open import real.epsilon-bounded.base
open import real.rational
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import subset
open import sequence
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import truncation
open import equivalence
open import funext


private
  simplify-path1 : {n : Nat} -> {x : ℝ} -> x * (ℕ->ℝ n * (x ^ℕ (pred n))) == (ℕ->ℝ n * (x ^ℕ n))
  simplify-path1 {zero} =
    *-right (*-left (Semiringʰ.preserves-0# Semiringʰ-ℕ->ℝ) >=> *-left-zero) >=>
    *-right-zero >=>
    sym *-left-zero >=>
    *-left (sym (Semiringʰ.preserves-0# Semiringʰ-ℕ->ℝ))
  simplify-path1 {suc n} = sym *-assoc >=> *-left *-commute >=> *-assoc

isDerivative-^ℕ : (n : ℕ) ->
  isDerivative (UnivS ℝ) (\(x , _) -> x ^ℕ n) (\(x , _) -> ℕ->ℝ n * x ^ℕ (pred n))
isDerivative-^ℕ zero =
  subst (isDerivative (UnivS ℝ) (\_ -> 1#)) (funExt (\(x , _) -> path x))
    (isDerivative-const 1#)
  where
  path : (x : ℝ) -> 0# == ℕ->ℝ 0 * x ^ℕ 0
  path x = sym (Semiringʰ.preserves-0# Semiringʰ-ℕ->ℝ) >=> sym *-right-one
isDerivative-^ℕ (suc n) =
  subst (isDerivative (UnivS ℝ) (\(x , _) -> x ^ℕ (suc n))) (funExt (\_ -> path))
    combined-d
  where
  left-d : isDerivative (UnivS ℝ) (\(x , _) -> x) (\_ -> 1#)
  left-d = isDerivative-id
  right-d : isDerivative (UnivS ℝ) (\(x , _) -> x ^ℕ n) (\(x , _) -> ℕ->ℝ n * x ^ℕ (pred n))
  right-d = isDerivative-^ℕ n
  combined-d : isDerivative (UnivS ℝ) (\(x , _) -> x ^ℕ (suc n))
                 (\(x , _) -> x * (ℕ->ℝ n * (x ^ℕ (pred n))) + (x ^ℕ n * 1#))
  combined-d = isDerivative-* left-d right-d

  path : {x : ℝ} -> x * (ℕ->ℝ n * (x ^ℕ (pred n))) + (x ^ℕ n * 1#) == ℕ->ℝ (suc n) * x ^ℕ n
  path =
    +-left simplify-path1 >=>
    +-right *-commute >=>
    +-commute >=>
    sym *-distrib-+-right >=>
    *-left (sym (Semiringʰ.preserves-+ Semiringʰ-ℕ->ℝ 1 n))
