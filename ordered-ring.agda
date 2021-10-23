{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import additive-group
open import base
open import equality
open import functions
open import hlevel
open import order
open import ordered-semiring
open import ring
open import semiring
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{R : Ring S AG}} where
  private
    module R = Ring R
    instance
      ILOS = LOS
      IACM = ACM
      IAG = AG
      IS = S
      IO = O
      IR = R

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

    *₁-preserves-< : {a b c : D} -> (0# < a) -> (b < c) -> (a * b) < (a * c)
    *₁-preserves-< {a} {b} {c} 0<a b<c = ab<ac
      where
      0<cb : 0# < (c + (- b))
      0<cb = subst2 _<_ +-inverse refl (+₂-preserves-< b<c)

      0<acb : 0# < (a * (c + (- b)))
      0<acb = *-preserves-0< 0<a 0<cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab<ac : (a * b) < (a * c)
      ab<ac = subst2 _<_ +-right-zero ab+acb=ac (+₁-preserves-< 0<acb)

    *₂-preserves-< : {a b c : D} -> (a < b) -> (0# < c) -> (a * c) < (b * c)
    *₂-preserves-< a<b 0<c =
      subst2 _<_ *-commute *-commute (*₁-preserves-< 0<c a<b)

    *₁-flips-< : {a b c : D} -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-< {a} {b} {c} a<0 b<c =
      subst2 _<_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-< (*₁-preserves-< 0<-a b<c))
      where
      0<-a : 0# < (- a)
      0<-a = (minus-flips-<0 a<0)

    *₂-flips-< : {a b c : D} -> (a < b) -> (c < 0#) -> (b * c) < (a * c)
    *₂-flips-< a<b c<0 =
      subst2 _<_ *-commute *-commute (*₁-flips-< c<0 a<b)

    *-flips-<0 : {a b : D} -> a < 0# -> b < 0# -> 0# < (a * b)
    *-flips-<0 {a} {b} a<0 b<0 = subst (_< (a * b)) *-left-zero (*₂-flips-< a<0 b<0)


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

    *₁-preserves-≮' : {a b c : D} -> (0# < a) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮' {a} {b} {c} 0<a = case-≮ c b (a * c) (a * b) (*₁-preserves-< 0<a) (cong (a *_))

  abstract
    *₁-preserves-≮ : {a b c : D} -> (a ≮ 0#) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮ {a} {b} {c} a≮0 b≮c = case-≮' 0# a (a * c) (a * b) f< f= a≮0
      where
      f= : (0# == a) -> a * c == a * b
      f= p = *-left (sym p) >=> *-left-zero >=> (sym *-left-zero) >=> *-left p

      f< : (0# < a) -> (a * b) ≮ (a * c)
      f< 0<a = *₁-preserves-≮' 0<a b≮c

    *₂-preserves-≮ : {a b c : D} -> (a ≮ b) -> (c ≮ 0#) -> (a * c) ≮ (b * c)
    *₂-preserves-≮ {a} {b} {c} a≮b c≮0 =
      subst2 _≮_ *-commute *-commute (*₁-preserves-≮ c≮0 a≮b)


    *-preserves-≮0 : {a b : D} -> (a ≮ 0#) -> (b ≮ 0#) -> (a * b) ≮ 0#
    *-preserves-≮0 {a} {b} a≮0 b≮0 = subst ((a * b) ≮_) *-right-zero (*₁-preserves-≮ a≮0 b≮0)

    +₁-preserves-≮ : {a b c : D} -> b ≮ c -> (a + b) ≮ (a + c)
    +₁-preserves-≮ b≮c ab<ac =
      b≮c (subst2 _<_ (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (+₁-preserves-< ab<ac))


    +-preserves-≮0 : {a b : D} -> a ≮ 0# -> b ≮ 0# -> (a + b) ≮ 0#
    +-preserves-≮0 {a} {b} a≮0 b≮0 ab<0 = unsquash isPropBot (∥-map handle (comparison-< ab a 0# ab<0))
      where
      ab = a + b
      handle : (ab < a) ⊎ (a < 0#) -> Bot
      handle (inj-r a<0) = a≮0 a<0
      handle (inj-l ab<a) =
        b≮0 (subst2 _<_ (sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero)
                        (+-commute >=> +-inverse) (+₁-preserves-< ab<a))

    1≮0# : 1# ≮ 0#
    1≮0# 1<0 = irrefl-< (trans-< -1<0 0<-1)
      where
      0<-1 = minus-flips-<0 1<0
      -1<0 = subst2 _<_ *-left-one *-left-one (*₁-flips-< 1<0 0<-1)

  abstract
    +₂-reflects-< : {a b c : D} -> (a + c) < (b + c) -> (a < b)
    +₂-reflects-< {a} {b} {c} ac<bc =
      subst2 _<_ (+-assoc >=> +-right +-inverse >=> +-right-zero)
                 (+-assoc >=> +-right +-inverse >=> +-right-zero)
                 (+₂-preserves-< ac<bc)

    +₁-reflects-< : {a b c : D} -> (a + b) < (a + c) -> (b < c)
    +₁-reflects-< ab<ac = +₂-reflects-< (subst2 _<_ +-commute +-commute ab<ac)

    +-reflects-< : {a b c d : D} -> (a + b) < (c + d) -> ∥ (a < c) ⊎ (b < d) ∥
    +-reflects-< {a} {b} {c} {d} ab<cd = ∥-map handle (comparison-< _ (c + b) _ ab<cd)
      where
      handle : ((a + b) < (c + b)) ⊎ ((c + b) < (c + d)) -> (a < c) ⊎ (b < d)
      handle = ⊎-map +₂-reflects-< +₁-reflects-<


module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : PartialOrderStr D ℓ<}
         {{POS : PartiallyOrderedSemiringStr S O}}
         {{R : Ring S AG}} where
  private
    instance
      IPOS = POS
      IACM = ACM
      IAG = AG
      IS = S
      IO = O
      IR = R

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

    *₁-preserves-≤ : {a b c : D} -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ {a} {b} {c} 0≤a b≤c = ab≤ac
      where
      0≤cb : 0# ≤ (c + (- b))
      0≤cb = subst2 _≤_ +-inverse refl (+₂-preserves-≤ b≤c)

      0≤acb : 0# ≤ (a * (c + (- b)))
      0≤acb = *-preserves-0≤ 0≤a 0≤cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab≤ac : (a * b) ≤ (a * c)
      ab≤ac = subst2 _≤_ +-right-zero ab+acb=ac (+₁-preserves-≤ 0≤acb)

    *₂-preserves-≤ : {a b c : D} -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ {a} {b} {c} a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ 0≤c a≤b)

    *₁-flips-≤ : {a b c : D} -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤ {a} {b} {c} a≤0 b≤c =
      subst2 _≤_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-≤ (*₁-preserves-≤ 0≤-a b≤c))
      where
      0≤-a : 0# ≤ (- a)
      0≤-a = (minus-flips-≤0 a≤0)

    *₂-flips-≤ : {a b c : D} -> (a ≤ b) -> (c ≤ 0#) -> (b * c) ≤ (a * c)
    *₂-flips-≤ {a} {b} {c} a≤b c≤0 =
      subst2 _≤_ *-commute *-commute (*₁-flips-≤ c≤0 a≤b)


module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : PartialOrderStr D ℓ≤}
         {{TO : TotalOrderStr O}}
         {{POS : PartiallyOrderedSemiringStr S O}}
         {{R : Ring S AG}} where
  private
    instance
      IPOS = POS
      ITO = TO
      IACM = ACM
      IS = S
      IO = O
      IR = R

  abstract
    0≤-square : {a : D} -> 0# ≤ (a * a)
    0≤-square {a} = unsquash (isProp-≤ _ _) (∥-map handle (connex-≤ 0# a))
      where
      handle : (0# ≤ a) ⊎ (a ≤ 0#) -> 0# ≤ (a * a)
      handle (inj-l 0≤a) = subst2 _≤_ *-right-zero refl (*₁-preserves-≤ 0≤a 0≤a)
      handle (inj-r a≤0) = subst2 _≤_ *-right-zero refl (*₁-flips-≤ a≤0 a≤0)
