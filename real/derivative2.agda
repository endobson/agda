{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2 where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import heyting-field.instances.real
open import nat
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import real
open import real.apartness
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import truncation

isSequentiallyContinuous :
  {ℓS : Level} -> (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) -> Type (ℓ-max ℓS ℓ-one)
isSequentiallyContinuous S f =
  ∀ (s : Sequence (∈-Subtype S)) -> (l : ∈-Subtype S) ->
    isLimit (\i -> ⟨ s i ⟩) ⟨ l ⟩ -> isLimit (\i -> f (s i)) (f l)

isProp-isSequentiallyContinuous :
  {ℓS : Level} -> (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) ->
  isProp (isSequentiallyContinuous S f)
isProp-isSequentiallyContinuous S f =
  isPropΠ3 (\ s l lim -> isProp-isLimit)



record LimitTestSeq {ℓS : Level} (S : Subtype ℝ ℓS) (x : ℝ) : Type (ℓ-max ℓS ℓ-one) where
  no-eta-equality
  field
    seq : Sequence ℝ
    S-seq : (n : ℕ) -> ⟨ S (seq n) ⟩
    seq#x : (n : ℕ) -> (seq n) # x
    isLimit-seq : isLimit seq x

  ∈S : Sequence (∈-Subtype S)
  ∈S n = seq n , S-seq n

isLimitPoint : {ℓS : Level} (S : Subtype ℝ ℓS) (x : ℝ) -> Type (ℓ-max ℓS ℓ-one)
isLimitPoint S x = ∥ LimitTestSeq S x ∥


isLimitPoint-UnivS : (x : ℝ) -> isLimitPoint (UnivS ℝ) x
isLimitPoint-UnivS x = ∣ test-seq ∣
  where
  test-seq : LimitTestSeq (UnivS ℝ) x
  test-seq .LimitTestSeq.seq n = x + harmonic-sequence n
  test-seq .LimitTestSeq.S-seq n = tt
  test-seq .LimitTestSeq.seq#x n =
    subst2 _#_ refl +-right-zero
      (+₁-preserves-# (inj-r (0<harmonic-sequence n)))
  test-seq .LimitTestSeq.isLimit-seq =
    subst2 isLimit refl +-right-zero
      (+-preserves-limit (isLimit-constant-seq x) isLimit-harmonic-sequence)

1/diff : {x y : ℝ} -> x # y -> ℝ
1/diff {x} {y} x#y = (ℝ1/ (diff x y) (eqFun diff-<>-equiv x#y))


record isLimitAt {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ℝ) (y : ℝ) :
                 Type (ℓ-max ℓS ℓ-one)
  where
  no-eta-equality
  field
    limit-point : isLimitPoint S x
    isLimit-∀seq : ∀ (t : LimitTestSeq S x) -> isLimit (f ∘ LimitTestSeq.∈S t) y

module _ {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x@(x' , _) : ∈-Subtype S) (y : ℝ) where
  private
    diff-seq : LimitTestSeq S x' -> Sequence ℝ
    diff-seq t i = diff (f (t.∈S i)) (f x) * 1/diff (t.seq#x i)
      where
      module t = LimitTestSeq t

  record isDerivativeAt : Type (ℓ-max ℓS ℓ-one) where
    field
      limit-point : isLimitPoint S x'
      isLimit-∀seq : ∀ (t : LimitTestSeq S x') -> isLimit (diff-seq t) y


isDerivative : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) ->
               Pred (∈-Subtype S -> ℝ) (ℓ-max ℓS ℓ-one)
isDerivative S f f' = ∀ (x : ∈-Subtype S) -> isDerivativeAt S f x (f' x)

isDifferentiable : {ℓS : Level} (S : Subtype ℝ ℓS) -> Pred (∈-Subtype S -> ℝ) (ℓ-max ℓS ℓ-one)
isDifferentiable S f = Σ (∈-Subtype S -> ℝ) (isDerivative S f)
