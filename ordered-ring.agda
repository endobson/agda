{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import base
open import equality
open import functions
open import hlevel
open import order
open import ordered-semiring
open import ring
open import semiring
open import truncation

private
  variable
    ℓD ℓ< : Level

record LinearlyOrderedRingStr {D : Type ℓD} {S : Semiring D} (R : Ring S) (O : LinearOrderStr D ℓ<)
  : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
  field
    ordered-semiring : LinearlyOrderedSemiringStr S O


module _ {D : Type ℓD} {S : Semiring D} {R : Ring S} {O : LinearOrderStr D ℓ<}
         {{LOR : LinearlyOrderedRingStr R O}} where
  private
    instance
      ILOS = LinearlyOrderedRingStr.ordered-semiring LOR
      IS = Ring.semiring R
      IO = O
      IR = R

  abstract
    minus-flips-< : (a b : D) -> (a < b) -> (- b) < (- a)
    minus-flips-< a b a<b =
      subst2 _<_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-< ((- b) + (- a)) a b a<b)

    *₁-preserves-< : (a b c : D) -> (0# < a) -> (b < c) -> (a * b) < (a * c)
    *₁-preserves-< a b c 0<a b<c = ab<ac
      where
      0<cb : 0# < (c + (- b))
      0<cb = subst2 _<_ +-inverse refl (+₂-preserves-< b c (- b) b<c)

      0<acb : 0# < (a * (c + (- b)))
      0<acb = *-preserves-0< a (c + (- b)) 0<a 0<cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab<ac : (a * b) < (a * c)
      ab<ac = subst2 _<_ +-right-zero ab+acb=ac (+₁-preserves-< (a * b) _ _ 0<acb)

  private
    case-≮' : (x y x' y' : D) -> (x < y -> y' ≮ x') -> (x == y -> x' == y') -> (y ≮ x -> y' ≮ x')
    case-≮' x y x' y' f< f= y≮x y'<x' = irrefl-< (subst (y' <_) x'==y' y'<x')
      where
      x≮y : x ≮ y
      x≮y x<y = f< x<y y'<x'

      x==y : x == y
      x==y = connected-< x≮y y≮x

      x'==y' : x' == y'
      x'==y' = f= x==y

    case-≮ : (x y x' y' : D) -> (x < y -> x' < y') -> (x == y -> x' == y') -> (y ≮ x -> y' ≮ x')
    case-≮ x y x' y' f< = case-≮' x y x' y' (asym-< ∘ f<)

    *₁-preserves-≮' : (a b c : D) -> (0# < a) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮' a b c 0<a = case-≮ c b (a * c) (a * b) (*₁-preserves-< a c b 0<a) (cong (a *_))

  abstract
    *₁-preserves-≮ : (a b c : D) -> (a ≮ 0#) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮ a b c a≮0 b≮c = case-≮' 0# a (a * c) (a * b) f< f= a≮0
      where
      f= : (0# == a) -> a * c == a * b
      f= p = *-left (sym p) >=> *-left-zero >=> (sym *-left-zero) >=> *-left p

      f< : (0# < a) -> (a * b) ≮ (a * c)
      f< 0<a = *₁-preserves-≮' a b c 0<a b≮c

    *-preserves-≮0 : (a b : D) -> (a ≮ 0#) -> (b ≮ 0#) -> (a * b) ≮ 0#
    *-preserves-≮0 a b a≮0 b≮0 = subst ((a * b) ≮_) *-right-zero (*₁-preserves-≮ a b 0# a≮0 b≮0)
