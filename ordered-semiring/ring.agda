{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.ring where

open import additive-group
open import base
open import equality
open import order
open import ordered-additive-group
open import ordered-semiring
open import semiring
open import relation
open import ring

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {O : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
         where
  private
    instance
      IACM = ACM
      IO = O

  LinearlyOrderedSemiringStr-Ring :
    (*₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)) ->
    LinearlyOrderedSemiringStr S O
  LinearlyOrderedSemiringStr-Ring *₁-preserves-< = record
    { *₁-preserves-< = *₁-preserves-<
    ; *₁-flips-< = *₁-flips-<'
    }
    where
    *₁-flips-<' : {a b c : D} -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-<' {a} {b} {c} a<0 b<c =
      subst2 _<_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-< (*₁-preserves-< 0<-a b<c))
      where
      module _ where
        0<-a : 0# < (- a)
        0<-a = trans-=-< (sym minus-zero) (minus-flips-< a<0)

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {O : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM O}}
         where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  PartiallyOrderedSemiringStr-Ring :
    (0≤1 : 0# ≤ 1#) ->
    (*₁-preserves-≤ : {a b c : D} -> 0# ≤ a -> b ≤ c -> (a * b) ≤ (a * c)) ->
    PartiallyOrderedSemiringStr S O
  PartiallyOrderedSemiringStr-Ring 0≤1 *₁-preserves-≤ = record
    { 0≤1 = 0≤1
    ; *₁-preserves-≤ = *₁-preserves-≤
    ; *₁-flips-≤ = *₁-flips-≤'
    }
    where
    *₁-flips-≤' : {a b c : D} -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤' {a} {b} {c} a≤0 b≤c =
      subst2 _≤_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-≤ (*₁-preserves-≤ 0≤-a b≤c))
      where
      module _ where
        0≤-a : 0# ≤ (- a)
        0≤-a = (minus-flips-≤0 a≤0)
