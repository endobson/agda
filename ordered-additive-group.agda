{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel.base
open import isomorphism
open import order
open import relation
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {D< : Rel D ℓ<} (ACM : AdditiveCommMonoid D) (O : isLinearOrder D<) where
  private
    instance
      IACM = ACM
      IO = O

  record LinearlyOrderedAdditiveStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      +₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)
      +₁-reflects-< : {a b c : D} -> (a + b) < (a + c) -> b < c

module _ {D : Type ℓD} {D< : Rel D ℓ<} {ACM : AdditiveCommMonoid D} {O : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}} where

  private
    module LOA = LinearlyOrderedAdditiveStr LOA
    instance
      IACM = ACM
      IO = O

  abstract
    +₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)
    +₁-preserves-< = LOA.+₁-preserves-<

    +₂-preserves-< : {a b c : D} -> a < b -> (a + c) < (b + c)
    +₂-preserves-< a<b = subst2 _<_ +-commute +-commute (+₁-preserves-< a<b)

    +-preserves-< : {a b c d : D} -> a < b -> c < d -> (a + c) < (b + d)
    +-preserves-< a<b c<d =
      trans-< (+₁-preserves-< c<d) (+₂-preserves-< a<b)

    +-preserves-0< : {a b : D} -> 0# < a -> 0# < b -> 0# < (a + b)
    +-preserves-0< {a} {b} 0<a 0<b =
      subst (_< (a + b)) +-right-zero (+-preserves-< 0<a 0<b)

    +-preserves-<0 : {a b : D} -> a < 0# -> b < 0# -> (a + b) < 0#
    +-preserves-<0 {a} {b} 0<a 0<b =
      subst ((a + b) <_) +-right-zero (+-preserves-< 0<a 0<b)

    +₁-reflects-< : {a b c : D} -> (a + b) < (a + c) -> b < c
    +₁-reflects-< = LOA.+₁-reflects-<

    +₂-reflects-< : {a b c : D} -> (a + c) < (b + c) -> a < b
    +₂-reflects-< ac<bc = +₁-reflects-< (subst2 _<_ +-commute +-commute ac<bc)

    +-reflects-< : {a b c d : D} -> (a + b) < (c + d) -> ∥ (a < c) ⊎ (b < d) ∥
    +-reflects-< {a} {b} {c} {d} ab<cd = ∥-map handle (comparison-< _ (c + b) _ ab<cd)
      where
      handle : ((a + b) < (c + b)) ⊎ ((c + b) < (c + d)) -> (a < c) ⊎ (b < d)
      handle = ⊎-map +₂-reflects-< +₁-reflects-<

    +-reflects-0< : {a b : D} -> 0# < (a + b) -> ∥ (0# < a) ⊎ (0# < b) ∥
    +-reflects-0< {a} {b} 0<ab = +-reflects-< (subst (_< (a + b)) (sym +-right-zero) 0<ab)

    +-reflects-<0 : {a b : D} -> (a + b) < 0# -> ∥ a < 0# ⊎ b < 0# ∥
    +-reflects-<0 a+b<0 = +-reflects-< (trans-<-= a+b<0 (sym +-right-zero))

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} (ACM : AdditiveCommMonoid D) (O : isPartialOrder D≤) where
  private
    instance
      IACM = ACM
      IO = O

  record PartiallyOrderedAdditiveStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    no-eta-equality
    field
      +₁-preserves-≤ : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D} {O : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM O}} where

  private
    module POA = PartiallyOrderedAdditiveStr POA
    instance
      IACM = ACM
      IO = O

  abstract
    +₁-preserves-≤ : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)
    +₁-preserves-≤ = POA.+₁-preserves-≤

    +₂-preserves-≤ : {a b c : D} -> a ≤ b -> (a + c) ≤ (b + c)
    +₂-preserves-≤ a≤b = subst2 _≤_ +-commute +-commute (+₁-preserves-≤ a≤b)

    +-preserves-≤ : {a b c d : D} -> a ≤ b -> c ≤ d -> (a + c) ≤ (b + d)
    +-preserves-≤ a≤b c≤d = trans-≤ (+₁-preserves-≤ c≤d) (+₂-preserves-≤ a≤b)

    +-preserves-0≤ : {a b : D} -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a + b)
    +-preserves-0≤ {a} {b} 0≤a 0≤b =
      subst (_≤ (a + b)) +-right-zero (+-preserves-≤ 0≤a 0≤b)

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} (ACM : AdditiveCommMonoid D) (PO : isPartialOrder D≤) where
  private
    instance
      IACM = ACM
      IPO = PO

  record StronglyPartiallyOrderedAdditiveStr : Type (ℓ-max ℓ≤ ℓD) where
    no-eta-equality
    field
      +₁-reflects-≤ : {a b c : D} -> (a + b) ≤ (a + c) -> b ≤ c

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D} {PO : isPartialOrder D≤}
         {{SPOA : StronglyPartiallyOrderedAdditiveStr ACM PO}} where

  private
    module SPOA = StronglyPartiallyOrderedAdditiveStr SPOA
    instance
      IACM = ACM
      IPO = PO

  abstract
    +₁-reflects-≤ : {a b c : D} -> (a + b) ≤ (a + c) -> b ≤ c
    +₁-reflects-≤ = SPOA.+₁-reflects-≤

    +₂-reflects-≤ : {a b c : D} -> (a + c) ≤ (b + c) -> a ≤ b
    +₂-reflects-≤ ac≤bc = +₁-reflects-≤ (subst2 _≤_ +-commute +-commute ac≤bc)


module _ {D : Type ℓD} {D< : Rel D ℓ<} {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {O : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
         where
  private
    instance
      IACM = ACM
      IO = O

  abstract
    minus-flips-< : {a b : D} -> (a < b) -> (- b) < (- a)
    minus-flips-< a<b =
      subst2 _<_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-< a<b)

    minus-flips-0< : {a : D} -> (0# < a) -> (- a) < 0#
    minus-flips-0< {a} 0<a = subst ((- a) <_) minus-zero (minus-flips-< 0<a)

    minus-flips-<0 : {a : D} -> (a < 0#) -> 0# < (- a)
    minus-flips-<0 {a} a<0 = subst (_< (- a)) minus-zero (minus-flips-< a<0)

    +₁-preserves-≮ : {a b c : D} -> b ≮ c -> (a + b) ≮ (a + c)
    +₁-preserves-≮ b≮c ab<ac =
      b≮c (subst2 _<_ (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (+₁-preserves-< ab<ac))

    +-preserves-≮0 : {a b : D} -> a ≮ 0# -> b ≮ 0# -> (a + b) ≮ 0#
    +-preserves-≮0 {a} {b} a≮0 b≮0 ab<0 = unsquash isPropBot (∥-map handle (comparison-< ab a 0# ab<0))
      where
      ab : D
      ab = a + b
      handle : (ab < a) ⊎ (a < 0#) -> Bot
      handle (inj-r a<0) = a≮0 a<0
      handle (inj-l ab<a) =
        b≮0 (subst2 _<_ (sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero)
                        (+-commute >=> +-inverse) (+₁-preserves-< ab<a))

    diff-0<⁺ : {a b : D} -> a < b -> 0# < diff a b
    diff-0<⁺ a<b = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)

    diff-0<⁻ : {a b : D} -> 0# < (diff a b) -> a < b
    diff-0<⁻ 0<ab =
      trans-=-< (sym +-right-zero) (trans-<-= (+₁-preserves-< 0<ab) diff-step)

    diff-<0⁺ : {a b : D} -> b < a -> (diff a b) < 0#
    diff-<0⁺ b<a =
      trans-=-< diff-anticommute (minus-flips-0< (diff-0<⁺ b<a))

    diff-<0⁻ : {a b : D} -> (diff a b) < 0# -> b < a
    diff-<0⁻ ab<0 =
      diff-0<⁻ (trans-<-= (minus-flips-<0 ab<0) (sym diff-anticommute))

    diff-<>-equiv : {a b : D} -> (a <> b) ≃ (diff a b <> 0#)
    diff-<>-equiv {a} {b} = isoToEquiv (isProp->iso forward backward isProp-<> isProp-<>)
      where
      forward : a <> b -> diff a b <> 0#
      forward = ⊎-swap ∘ ⊎-map diff-0<⁺ diff-<0⁺
      backward : diff a b <> 0# -> a <> b
      backward = ⊎-swap ∘ ⊎-map diff-<0⁻ diff-0<⁻


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {O : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM O}}
         where
  private
    instance
      IACM = ACM
      IO = O

  abstract
    minus-flips-≤ : {a b : D} -> (a ≤ b) -> (- b) ≤ (- a)
    minus-flips-≤ {a} {b} a≤b =
      subst2 _≤_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-≤ a≤b)

    minus-flips-0≤ : {a : D} -> (0# ≤ a) -> (- a) ≤ 0#
    minus-flips-0≤ {a} 0≤a = subst ((- a) ≤_) minus-zero (minus-flips-≤ 0≤a)

    minus-flips-≤0 : {a : D} -> (a ≤ 0#) -> 0# ≤ (- a)
    minus-flips-≤0 {a} a≤0 = subst (_≤ (- a)) minus-zero (minus-flips-≤ a≤0)

    diff-0≤⁺ : {a b : D} -> a ≤ b -> 0# ≤ diff a b
    diff-0≤⁺ a≤b = trans-=-≤ (sym +-inverse) (+₂-preserves-≤ a≤b)

    diff-0≤⁻ : {a b : D} -> 0# ≤ (diff a b) -> a ≤ b
    diff-0≤⁻ 0≤ab =
      trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ 0≤ab) diff-step)

    diff-≤0⁺ : {a b : D} -> b ≤ a -> diff a b ≤ 0#
    diff-≤0⁺ a≤b =
      trans-=-≤ diff-anticommute (minus-flips-0≤ (diff-0≤⁺ a≤b))

    diff-≤0⁻ : {a b : D} -> (diff a b) ≤ 0# -> b ≤ a
    diff-≤0⁻ 0≤ab =
     diff-0≤⁻ (trans-≤-= (minus-flips-≤0 0≤ab) (sym diff-anticommute))
