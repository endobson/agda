{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel.sigma
open import isomorphism
open import order
open import semiring
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

-- TODO rename this to just about the multiplicative structure
module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : LinearOrderStr D ℓ<) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record LinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      *₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)
      *₁-flips-< : {a b c : D} -> a < 0# -> b < c -> (a * c) < (a * b)

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}} where

  private
    module LOS = LinearlyOrderedSemiringStr LOS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    *₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)
    *₁-preserves-< = LOS.*₁-preserves-<

    *₂-preserves-< : {a b c : D} -> a < b -> 0# < c -> (a * c) < (b * c)
    *₂-preserves-< a<b 0<c =
      subst2 _<_ *-commute *-commute (*₁-preserves-< 0<c a<b)

    *-preserves-0< : {a b : D} -> 0# < a -> 0# < b -> 0# < (a * b)
    *-preserves-0< 0<a 0<b = trans-=-< (sym *-right-zero) (LOS.*₁-preserves-< 0<a 0<b)

    *₁-flips-< : {a b c : D} -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-< = LOS.*₁-flips-<

    *₂-flips-< : {a b c : D} -> (a < b) -> (c < 0#) -> (b * c) < (a * c)
    *₂-flips-< a<b c<0 =
      subst2 _<_ *-commute *-commute (*₁-flips-< c<0 a<b)

    *₁-preserves-<0 : {a b : D} -> 0# < a -> b < 0# -> (a * b) < 0#
    *₁-preserves-<0 0<a b<0 =
      trans-<-= (*₂-flips-< 0<a b<0) *-left-zero

    *₂-preserves-<0 : {a b : D} -> a < 0# -> 0# < b -> (a * b) < 0#
    *₂-preserves-<0 a<0 0<b =
      trans-<-= (*₁-flips-< a<0 0<b) *-right-zero

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


module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : LinearOrderStr D ℓ<) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record StronglyLinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      *₁-fully-reflects-< : {a b c : D} -> (a * b) < (a * c) ->
        (b < c × 0# < a) ⊎ (c < b × a < 0#)

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S O}} where
  private
    module SLOS = StronglyLinearlyOrderedSemiringStr SLOS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    *₁-fully-reflects-< : {a b c : D} -> (a * b) < (a * c) ->
                          (b < c × 0# < a) ⊎ (c < b × a < 0#)
    *₁-fully-reflects-< = SLOS.*₁-fully-reflects-<

    *₁-reflects-< : {a b c : D} -> (a ≮ 0#) -> (a * b) < (a * c) -> (b < c)
    *₁-reflects-< a≮0 ab<ac =
      proj₁ (proj-¬r (*₁-fully-reflects-< ab<ac) (\ (c<b , a<0) -> a≮0 a<0))

    *₁-flip-reflects-< : {a b c : D} -> (a ≯ 0#) -> (a * b) < (a * c) -> (c < b)
    *₁-flip-reflects-< a≯0 ab<ac =
      proj₁ (proj-¬l (*₁-fully-reflects-< ab<ac) (\ (c<b , a>0) -> a≯0 a>0))

    *₂-reflects-< : {a b c : D} -> (a * c) < (b * c) -> (c ≮ 0#) -> (a < b)
    *₂-reflects-< {a} {b} {c} ac<bc c≮0 =
      *₁-reflects-< c≮0 (subst2 _<_ *-commute *-commute ac<bc)

    *₂-flip-reflects-< : {a b c : D} -> (a * c) < (b * c) -> (c ≯ 0#) -> (b < a)
    *₂-flip-reflects-< {a} {b} {c} ac<bc c≯0 =
      *₁-flip-reflects-< c≯0 (subst2 _<_ *-commute *-commute ac<bc)

    *₁-reflects-0< : {a b : D} -> (a ≮ 0#) -> 0# < (a * b) -> (0# < b)
    *₁-reflects-0< {a} {b} a≮0 0<ab =
      *₁-reflects-< a≮0 (subst (_< (a * b)) (sym *-right-zero) 0<ab)

    *₁-flip-reflects-0< : {a b : D} -> (a ≯ 0#) -> 0# < (a * b) -> (b < 0#)
    *₁-flip-reflects-0< {a} {b} a≯0 0<ab =
      *₁-flip-reflects-< a≯0 (subst (_< (a * b)) (sym *-right-zero) 0<ab)

    *₂-reflects-0< : {a b : D} -> 0# < (a * b) -> (b ≮ 0#) -> (0# < a)
    *₂-reflects-0< {a} {b} 0<ab b≮0 =
      *₂-reflects-< (subst (_< (a * b)) (sym *-left-zero) 0<ab) b≮0

    *₂-flip-reflects-0< : {a b : D} -> 0# < (a * b) -> (b ≯ 0#) -> (a < 0#)
    *₂-flip-reflects-0< {a} {b} 0<ab b≯0 =
      *₂-flip-reflects-< (subst (_< (a * b)) (sym *-left-zero) 0<ab) b≯0

    *-reflects-<>0 : {a b : D} -> (a * b) <> 0# -> (a <> 0# × b <> 0#)
    *-reflects-<>0 {a} {b} (inj-l ab<0) =
      handle (*₁-fully-reflects-< (subst ((a * b) <_) (sym *-right-zero) ab<0))
      where
      handle : (b < 0# × 0# < a) ⊎ (0# < b × a < 0#) -> (a <> 0# × b <> 0#)
      handle (inj-l (b<0 , 0<a)) = inj-r 0<a , inj-l b<0
      handle (inj-r (0<b , a<0)) = inj-l a<0 , inj-r 0<b
    *-reflects-<>0 {a} {b} (inj-r 0<ab) =
      handle (*₁-fully-reflects-< (subst (_< (a * b)) (sym *-right-zero) 0<ab))
      where
      handle : (0# < b × 0# < a) ⊎ (b < 0# × a < 0#) -> (a <> 0# × b <> 0#)
      handle (inj-l (0<b , 0<a)) = inj-r 0<a , inj-r 0<b
      handle (inj-r (b<0 , a<0)) = inj-l a<0 , inj-l b<0

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S O}} where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  *-<>0-equiv : {a b : D} -> ((a <> 0#) × (b <> 0#)) ≃ (a * b) <> 0#
  *-<>0-equiv {a} {b} =
    isoToEquiv (isProp->iso *-preserves-<>0 *-reflects-<>0 (isProp× isProp-<> isProp-<>) isProp-<>)
    where
    *-preserves-<>0 : ((a <> 0#) × (b <> 0#)) -> (a * b) <> 0#
    *-preserves-<>0 (inj-l a<0 , inj-l b<0) = inj-r (*-flips-<0 a<0 b<0)
    *-preserves-<>0 (inj-l a<0 , inj-r 0<b) = inj-l (*₂-preserves-<0 a<0 0<b)
    *-preserves-<>0 (inj-r 0<a , inj-l b<0) = inj-l (*₁-preserves-<0 0<a b<0)
    *-preserves-<>0 (inj-r 0<a , inj-r 0<b) = inj-r (*-preserves-0< 0<a 0<b)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : PartialOrderStr D ℓ≤) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record PartiallyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    no-eta-equality
    field
      *₁-preserves-≤ : {a b c : D} -> 0# ≤ a -> b ≤ c -> (a * b) ≤ (a * c)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {O : PartialOrderStr D ℓ<}
         {{POS : PartiallyOrderedSemiringStr S O}} where

  private
    module POS = PartiallyOrderedSemiringStr POS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    *-preserves-0≤ : {a b : D} -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a * b)
    *-preserves-0≤ 0≤a 0≤b = trans-=-≤ (sym *-right-zero) (POS.*₁-preserves-≤ 0≤a 0≤b)

    *₁-preserves-≤ : {a b c : D} -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ = POS.*₁-preserves-≤

    *₂-preserves-≤ : {a b c : D} -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ {a} {b} {c} a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ 0≤c a≤b)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         (S : Semiring ACM) (LO : LinearOrderStr D ℓ<) (PO : PartialOrderStr D ℓ≤) where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO
      IPO = PO

  record StronglyPartiallyOrderedSemiringStr : Type (ℓ-max* 3 ℓ< ℓ≤ ℓD) where
    no-eta-equality
    field
      *₁-reflects-≤ : {a b c : D} -> 0# < a -> (a * b) ≤ (a * c) -> b ≤ c
      *₁-flip-reflects-≤ : {a b c : D} -> a < 0# -> (a * b) ≤ (a * c) -> c ≤ b

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
         {{SPOS : StronglyPartiallyOrderedSemiringStr S LO PO}} where

  private
    module SPOS = StronglyPartiallyOrderedSemiringStr SPOS
    instance
      IACM = ACM
      IS = S
      IPO = PO
      ILO = LO

  abstract
    *₁-reflects-≤ : {a b c : D} -> (0# < a) -> (a * b) ≤ (a * c) -> (b ≤ c)
    *₁-reflects-≤ = SPOS.*₁-reflects-≤

    *₂-reflects-≤ : {a b c : D} -> (a * c) ≤ (b * c) -> (0# < c) -> (a ≤ b)
    *₂-reflects-≤ {a} {b} {c} ac≤bc 0<c =
      *₁-reflects-≤ 0<c (subst2 _≤_ *-commute *-commute ac≤bc)
