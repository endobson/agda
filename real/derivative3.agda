{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3 where

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
open import metric-space
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.minmax
open import ordered-additive-group.absolute-value
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
open import real.subspace
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation

{-
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
-}



record LimitTestSeq {ℓS : Level} (S : Subtype ℝ ℓS) (x : ℝ) : Type (ℓ-max ℓS ℓ-one) where
  no-eta-equality
  field
    seq : Sequence ℝ
    S-seq : (n : ℕ) -> ⟨ S (seq n) ⟩
    seq#x : (n : ℕ) -> (seq n) # x
    isLimit-seq : isLimit seq x

  ∈S : Sequence (Subspace S)
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


record isLimitAt {ℓS : Level} (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) (x : ℝ) (y : ℝ) :
                 Type (ℓ-max ℓS ℓ-one)
  where
  no-eta-equality
  field
    limit-point : isLimitPoint S x
    distance<ε :
      ∀ ((ε , _) : ℝ⁺) -> ∃[ (δ , _) ∈ ℝ⁺ ]
        (∀ (x'∈@(x' , _) : Subspace S) ->
          distance x x' < δ -> distance y (f x'∈) < ε)

slope : {ℓS : Level} (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) ->
        ((x , _) (y , _) : Subspace S) -> (x # y) -> ℝ
slope S f x∈@(x , _) y∈@(y , _) x#y = diff (f x∈) (f y∈) * 1/diff x#y

#S : ℝ -> Subtype ℝ ℓ-one
#S x y = x # y , isProp-#

Subtype-∩ : {ℓD ℓ₁ ℓ₂ : Level} {D : Type ℓD} -> Subtype D ℓ₁ -> Subtype D ℓ₂ -> Subtype D (ℓ-max ℓ₁ ℓ₂)
Subtype-∩ S1 S2 x = (fst (S1 x) × fst (S2 x)) , isProp× (snd (S1 x)) (snd (S2 x))

module _ {ℓS : Level} (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) (x∈@(x , _) : Subspace S) (d : ℝ) where
  record isDerivativeAt : Type (ℓ-max ℓS ℓ-one) where
    field
      limit-point : isLimitPoint S x
      distance<ε :
        ∀ ((ε , _) : ℝ⁺) -> ∃[ (δ , _) ∈ ℝ⁺ ]
          (∀ (x'∈@(x' , _) : Subspace S) -> (x#x' : x # x') ->
            distance x x' < δ -> distance (slope S f x∈ x'∈ x#x') d < ε)

isDerivative : {ℓS : Level} (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) ->
               Pred (Subspace S -> ℝ) (ℓ-max ℓS ℓ-one)
isDerivative S f f' = ∀ (x : Subspace S) -> isDerivativeAt S f x (f' x)

isDifferentiable : {ℓS : Level} (S : Subtype ℝ ℓS) -> Pred (Subspace S -> ℝ) (ℓ-max ℓS ℓ-one)
isDifferentiable S f = Σ (Subspace S -> ℝ) (isDerivative S f)
