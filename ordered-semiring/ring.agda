{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.ring where

open import additive-group
open import base
open import equality
open import order
open import ordered-semiring
open import semiring
open import ring

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {{O : LinearOrderStr D ℓ<}} where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S

  LinearlyOrderedSemiringStr-Ring :
    (+₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)) ->
    (*₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)) ->
    LinearlyOrderedSemiringStr S O
  LinearlyOrderedSemiringStr-Ring +₁-preserves-< *₁-preserves-< = record
    { +₁-preserves-< = +₁-preserves-<
    ; *₁-preserves-< = *₁-preserves-<
    ; *₁-flips-< = *₁-flips-<'
    }
    where
    minus-flips-< : {a b : D} -> (a < b) -> (- b) < (- a)
    minus-flips-< a<b =
      subst2 _<_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-< a<b)

    *₁-flips-<' : {a b c : D} -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-<' {a} {b} {c} a<0 b<c =
      subst2 _<_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-< (*₁-preserves-< 0<-a b<c))
      where
      module _ where
        0<-a : 0# < (- a)
        0<-a = trans-=-< (sym minus-zero) (minus-flips-< a<0)
