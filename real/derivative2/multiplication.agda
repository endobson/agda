{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.multiplication where

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
open import ring
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

  isDerivative-* : isDerivative S (\x -> f x * g x) (\x -> f x * g' x + g x * f' x)
  isDerivative-* x .isDerivativeAt.limit-point = isDerivativeAt.limit-point (df x)
  isDerivative-* x .isDerivativeAt.isLimit-∀seq t = lim
    where
    module t = LimitTestSeq t
    diff-seq : Sequence ℝ
    diff-seq i = diff (f (t.∈S i) * (g (t.∈S i))) (f x * g x) *
                 (1/diff (t.seq#x i))

    path2 : {a b ai bi : ℝ} -> ai * (diff bi b) + b * (diff ai a) == diff (ai * bi) (a * b)
    path2 =
      +-cong *-distrib-diff-left *-distrib-diff-left >=>
      +-left (+-left *-commute) >=>
      diff-trans >=>
      +-left *-commute

    path : ∀ i -> f (t.∈S i) * (diff (g (t.∈S i)) (g x) * 1/diff (t.seq#x i)) +
                  g x * (diff (f (t.∈S i)) (f x) * 1/diff (t.seq#x i)) ==
                  diff-seq i
    path i =
      +-cong (sym *-assoc) (sym *-assoc) >=>
      sym *-distrib-+-right >=>
      *-left path2

    lim-d : isLimit (\i -> diff (t.seq i) ⟨ x ⟩) 0#
    lim-d =
      subst2 isLimit refl +-inverse
        (+-preserves-limit
          (isLimit-constant-seq ⟨ x ⟩)
          (minus-preserves-limit t.isLimit-seq))


    lim-f : isLimit (\i -> diff (f (t.∈S i)) (f x) * 1/diff (t.seq#x i)) (f' x)
    lim-f = isDerivativeAt.isLimit-∀seq (df x) t

    lim-f2 : isLimit (\i -> diff (f (t.∈S i)) (f x)) 0#
    lim-f2 =
      subst2 isLimit (funExt (\_ -> *-assoc >=> *-right (ℝ1/-inverse _ _) >=> *-right-one))
                     *-right-zero
        (*-preserves-limit lim-f lim-d)


    lim-fi : isLimit (\i -> f (t.∈S i)) (f x)
    lim-fi =
      subst2 isLimit (funExt (\i -> +-right (sym diff-anticommute) >=> diff-step))
                     (+-right minus-zero >=> +-right-zero)
        (+-preserves-limit
          (isLimit-constant-seq (f x))
          (minus-preserves-limit lim-f2))


    lim1 : isLimit (\i -> f (t.∈S i) * (diff (g (t.∈S i)) (g x) * 1/diff (t.seq#x i))) (f x * (g' x))
    lim1 = *-preserves-limit lim-fi (isDerivativeAt.isLimit-∀seq (dg x) t)

    lim2 : isLimit (\i -> g x * (diff (f (t.∈S i)) (f x) * 1/diff (t.seq#x i))) (g x * f' x)
    lim2 = *₁-preserves-limit (isDerivativeAt.isLimit-∀seq (df x) t)
    lim3 : isLimit (\i -> f (t.∈S i) * (diff (g (t.∈S i)) (g x) * 1/diff (t.seq#x i)) +
                          g x * (diff (f (t.∈S i)) (f x) * 1/diff (t.seq#x i)))
                   (f x * g' x + g x * f' x)
    lim3 = +-preserves-limit lim1 lim2

    lim : isLimit diff-seq (f x * g' x + g x * f' x)
    lim = subst2 isLimit (funExt path) refl lim3
