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

module _ {D : Type ℓD} {S : Semiring D} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{R : Ring S}} where
  private
    instance
      ILOS = LOS
      IS = S
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

    *₂-preserves-< : (a b c : D) -> (a < b) -> (0# < c) -> (a * c) < (b * c)
    *₂-preserves-< a b c a<b 0<c =
      subst2 _<_ *-commute *-commute (*₁-preserves-< c a b 0<c a<b)

    *₁-flips-< : (a b c : D) -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-< a b c a<0 b<c =
      subst2 _<_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-< _ _ (*₁-preserves-< (- a) b c 0<-a b<c))
      where
      0<-a : 0# < (- a)
      0<-a = subst (_< (- a)) minus-zero (minus-flips-< _ _ a<0)

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

    *₂-preserves-≮ : (a b c : D) -> (a ≮ b) -> (c ≮ 0#) -> (a * c) ≮ (b * c)
    *₂-preserves-≮ a b c a≮b c≮0 =
      subst2 _≮_ *-commute *-commute (*₁-preserves-≮ c a b c≮0 a≮b)


    *-preserves-≮0 : (a b : D) -> (a ≮ 0#) -> (b ≮ 0#) -> (a * b) ≮ 0#
    *-preserves-≮0 a b a≮0 b≮0 = subst ((a * b) ≮_) *-right-zero (*₁-preserves-≮ a b 0# a≮0 b≮0)


module _ {D : Type ℓD} {S : Semiring D} {O : TotalOrderStr D ℓ<}
         {{TOS : TotallyOrderedSemiringStr S O}}
         {{R : Ring S}} where
  private
    instance
      ITOS = TOS
      IS = S
      IO = O
      IR = R

  abstract
    minus-flips-≤ : (a b : D) -> (a ≤ b) -> (- b) ≤ (- a)
    minus-flips-≤ a b a≤b =
      subst2 _≤_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-≤ ((- b) + (- a)) a b a≤b)

    *₁-preserves-≤ : (a b c : D) -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ a b c 0≤a b≤c = ab≤ac
      where
      0≤cb : 0# ≤ (c + (- b))
      0≤cb = subst2 _≤_ +-inverse refl (+₂-preserves-≤ b c (- b) b≤c)

      0≤acb : 0# ≤ (a * (c + (- b)))
      0≤acb = *-preserves-0≤ a (c + (- b)) 0≤a 0≤cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab≤ac : (a * b) ≤ (a * c)
      ab≤ac = subst2 _≤_ +-right-zero ab+acb=ac (+₁-preserves-≤ (a * b) _ _ 0≤acb)

    *₂-preserves-≤ : (a b c : D) -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ a b c a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ c a b 0≤c a≤b)

    *₁-flips-≤ : (a b c : D) -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤ a b c a≤0 b≤c =
      subst2 _≤_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-≤ _ _ (*₁-preserves-≤ (- a) b c 0≤-a b≤c))
      where
      0≤-a : 0# ≤ (- a)
      0≤-a = subst (_≤ (- a)) minus-zero (minus-flips-≤ _ _ a≤0)

    *₂-flips-≤ : (a b c : D) -> (a ≤ b) -> (c ≤ 0#) -> (b * c) ≤ (a * c)
    *₂-flips-≤ a b c a≤b c≤0 =
      subst2 _≤_ *-commute *-commute (*₁-flips-≤ c a b c≤0 a≤b)
