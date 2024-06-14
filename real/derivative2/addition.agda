{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.addition where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import heyting-field.instances.rational
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group.instances.rational
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative2
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.epsilon-bounded
open import real.rational
open import real.sequence.limit-point
open import ring.implementations.real
open import semiring
open import truncation
open import subset
open import sequence
open import funext

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f f' g g' : ∈-Subtype S -> ℝ}
         (df : isDerivative S f f') (dg : isDerivative S g g') where

  isDerivative-+ : isDerivative S (\x -> f x + g x) (\x -> f' x + g' x)
  isDerivative-+ x .isDerivativeAt.limit-point = isDerivativeAt.limit-point (df x)
  isDerivative-+ x .isDerivativeAt.isLimit-∀seq t = lim
    where
    module t = LimitTestSeq t
    diff-seq : Sequence ℝ
    diff-seq i = diff (f (t.∈S i) + (g (t.∈S i))) (f x + g x) * (1/diff (t.seq#x i))

    path : ∀ i -> diff (f (t.∈S i)) (f x) * (1/diff (t.seq#x i)) +
                  diff (g (t.∈S i)) (g x) * (1/diff (t.seq#x i)) ==
                  diff-seq i
    path i = sym *-distrib-+-right >=> *-left +-swap-diff

    lim : isLimit diff-seq (f' x + g' x)
    lim =
      subst2 isLimit (funExt path) refl
        (+-preserves-limit (isDerivativeAt.isLimit-∀seq (df x) t)
                           (isDerivativeAt.isLimit-∀seq (dg x) t))
