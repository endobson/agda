{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.minmax
open import rational
open import rational.order
open import relation
open import semiring
open import sum

private
  variable
    ℓ : Level

record Iℚ : Type₀ where
  no-eta-equality ; pattern
  constructor Iℚ-cons
  field
    l : ℚ
    u : ℚ
    l<u : l ℚ< u

opaque
  Iℚ-bounds-path : {a b : Iℚ} -> (Iℚ.l a == Iℚ.l b) -> (Iℚ.u a == Iℚ.u b) -> a == b
  Iℚ-bounds-path {a@(Iℚ-cons _ _ _)} {b@(Iℚ-cons _ _ _)} pl pu i = Iℚ-cons (pl i) (pu i) (p< i)
    where
    p< : PathP (\i -> (pl i) < (pu i)) (Iℚ.l<u a) (Iℚ.l<u b)
    p< = isProp->PathP (\i -> isProp-<)


ℚ∈Iℚ : ℚ -> Pred Iℚ ℓ-zero
ℚ∈Iℚ q a = (Iℚ.l a < q) × (q < Iℚ.u a)


-- Interval operations

i-_ : Iℚ -> Iℚ
i-_ a = Iℚ-cons (- a.u) (- a.l) (minus-flips-< a.l<u)
  where
  module a = Iℚ a

i--double-inverse : {a : Iℚ} -> (i- (i- a)) == a
i--double-inverse = Iℚ-bounds-path minus-double-inverse minus-double-inverse


_i+_ : Iℚ -> Iℚ -> Iℚ
_i+_ a b = Iℚ-cons (a.l + b.l) (a.u + b.u) lt
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (a.l + b.l) < (a.u + b.u)
    lt = (+-preserves-< a.l<u b.l<u)

i+-commute : (a b : Iℚ) -> a i+ b == b i+ a
i+-commute _ _ = Iℚ-bounds-path +-commute +-commute

i+-assoc : (a b c : Iℚ) -> (a i+ b) i+ c == a i+ (b i+ c)
i+-assoc _ _ _ = Iℚ-bounds-path +-assoc +-assoc

_i∪_ : Iℚ -> Iℚ -> Iℚ
_i∪_ a b = (Iℚ-cons (min a.l b.l) (max a.u b.u) lt)
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (min a.l b.l) < (max a.u b.u)
    lt = (trans-<-≤ (trans-≤-< min-≤-left a.l<u) max-≤-left)

i∪-commute : (a b : Iℚ) -> a i∪ b == b i∪ a
i∪-commute a b = Iℚ-bounds-path min-commute max-commute

i∪-assoc : (a b c : Iℚ) -> (a i∪ b) i∪ c == a i∪ (b i∪ c)
i∪-assoc a b c = Iℚ-bounds-path min-assoc max-assoc

i∪-same : (a : Iℚ) -> a i∪ a == a
i∪-same a = Iℚ-bounds-path min-idempotent max-idempotent

i-scale⁺ : (k : ℚ⁺) -> Iℚ -> Iℚ
i-scale⁺ (k , 0<k) a =
  Iℚ-cons (k * a.l) (k * a.u) (*₁-preserves-< 0<k a.l<u)
  where
  module a = Iℚ a

i-scale⁻ : (k : ℚ⁻) -> Iℚ -> Iℚ
i-scale⁻ (k , k<0) a =
  Iℚ-cons (k * a.u) (k * a.l) (*₁-flips-< k<0 a.l<u)
  where
  module a = Iℚ a

i-scale : (k : ℚ) -> (k <> 0#)-> Iℚ -> Iℚ
i-scale k k<>0 a = Iℚ-cons min' max' lt
  where
  module a = Iℚ a
  min' = min (k * a.l) (k * a.u)
  max' = max (k * a.l) (k * a.u)
  handle⁺ : (0# < k) -> min' < max'
  handle⁺ 0<k =
    trans-=-< (sym (*-distrib-min-left (weaken-< 0<k)))
      (trans-<-=
        (*₁-preserves-< 0<k (trans-≤-< min-≤-left (trans-<-≤ a.l<u max-≤-right)))
        (*-distrib-max-left (weaken-< 0<k)))

  handle⁻ : (k < 0#) -> min' < max'
  handle⁻ k<0 =
    trans-=-< (sym (*-distrib-flip-max-left (weaken-< k<0)))
      (trans-<-=
        (*₁-flips-< k<0 (trans-≤-< min-≤-left (trans-<-≤ a.l<u max-≤-right)))
        (*-distrib-flip-min-left (weaken-< k<0)))

  opaque
    lt : min' < max'
    lt = either handle⁻ handle⁺ k<>0
