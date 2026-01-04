{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import order
open import order.homomorphism
open import ordered-additive-group
open import relation
open import semiring
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

-- TODO rename this to just about the multiplicative structure
module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : isLinearOrder D<) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record LinearlyOrderedSemiringStr : Type (ℓ-max ℓ< ℓD) where
    no-eta-equality
    field
      *₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)
      *₁-flips-< : {a b c : D} -> a < 0# -> b < c -> (a * c) < (a * b)

module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}} {{O : isLinearOrder D<}}
         {{LOS : LinearlyOrderedSemiringStr S O}} where

  private
    module LOS = LinearlyOrderedSemiringStr LOS

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

    1≮0 : 1# ≮ 0#
    1≮0 1<0 = asym-< (trans-<-= (*-flips-<0 1<0 1<0) *-left-one) 1<0

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

    *₁-flips-≮' : {a b c : D} -> (a < 0#) -> (b ≮ c) -> (a * c) ≮ (a * b)
    *₁-flips-≮' {a} {b} {c} a<0 = case-≮ c b (a * b) (a * c) (*₁-flips-< a<0) (cong (a *_) ∘ sym)

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

    *₁-flips-≮ : {a b c : D} -> (0# ≮ a) -> (b ≮ c) -> (a * c) ≮ (a * b)
    *₁-flips-≮ {a} {b} {c} 0≮a b≮c = case-≮' a 0# (a * b) (a * c) f< f= 0≮a
      where
      f= : (a == 0#) -> a * b == a * c
      f= p = *-left p >=> *-left-zero >=> (sym *-left-zero) >=> *-left (sym p)

      f< : (a < 0#) -> (a * c) ≮ (a * b)
      f< 0<a = *₁-flips-≮' 0<a b≮c


module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : isLinearOrder D<) where
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

module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}} {{O : isLinearOrder D<}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S O}} where
  private
    module SLOS = StronglyLinearlyOrderedSemiringStr SLOS

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

module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}} {{O : isLinearOrder D<}}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S O}}
  where

  *-<>0-equiv : {a b : D} -> ((a <> 0#) × (b <> 0#)) ≃ (a * b) <> 0#
  *-<>0-equiv {a} {b} =
    isoToEquiv (isProp->iso *-preserves-<>0 *-reflects-<>0 (isProp× isProp-<> isProp-<>) isProp-<>)
    where
    *-preserves-<>0 : ((a <> 0#) × (b <> 0#)) -> (a * b) <> 0#
    *-preserves-<>0 (inj-l a<0 , inj-l b<0) = inj-r (*-flips-<0 a<0 b<0)
    *-preserves-<>0 (inj-l a<0 , inj-r 0<b) = inj-l (*₂-preserves-<0 a<0 0<b)
    *-preserves-<>0 (inj-r 0<a , inj-l b<0) = inj-l (*₁-preserves-<0 0<a b<0)
    *-preserves-<>0 (inj-r 0<a , inj-r 0<b) = inj-r (*-preserves-0< 0<a 0<b)

  opaque
    non-trivial-0<1 : {a b : D} -> a < b -> 0# < 1#
    non-trivial-0<1 {a} {b} a<b =
      proj₂ (proj-¬r (*₁-fully-reflects-< 1a<1b) (\ (_ , 1<0) -> 1≮0 1<0))
      where
      1a<1b : (1# * a) < (1# * b)
      1a<1b = trans-=-< *-left-one (trans-<-= a<b (sym *-left-one))


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : isPartialOrder D≤) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record PartiallyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    no-eta-equality
    field
      0≤1 : D≤ 0# 1#
      *₁-preserves-≤ : {a b c : D} -> 0# ≤ a -> b ≤ c -> (a * b) ≤ (a * c)
      *₁-flips-≤ : {a b c : D} -> a ≤ 0# -> b ≤ c -> (a * c) ≤ (a * b)


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}} {{O : isPartialOrder D≤}}
         {{POS : PartiallyOrderedSemiringStr S O}} where

  private
    module POS = PartiallyOrderedSemiringStr POS

  abstract
    0≤1 : 0# ≤ 1#
    0≤1 = POS.0≤1

    *-preserves-0≤ : {a b : D} -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a * b)
    *-preserves-0≤ 0≤a 0≤b = trans-=-≤ (sym *-right-zero) (POS.*₁-preserves-≤ 0≤a 0≤b)

    *₁-preserves-≤ : {a b c : D} -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ = POS.*₁-preserves-≤

    *₂-preserves-≤ : {a b c : D} -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ {a} {b} {c} a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ 0≤c a≤b)

    *₁-flips-≤ : {a b c : D} -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤ = POS.*₁-flips-≤

    *₂-flips-≤ : {a b c : D} -> (a ≤ b) -> (c ≤ 0#) -> (b * c) ≤ (a * c)
    *₂-flips-≤ {a} {b} {c} a≤b c≤0 =
      subst2 _≤_ *-commute *-commute (*₁-flips-≤ c≤0 a≤b)

    *₁-preserves-≤0 : {a b : D} -> 0# ≤ a -> b ≤ 0# -> (a * b) ≤ 0#
    *₁-preserves-≤0 0≤a b≤0 =
      trans-≤-= (*₂-flips-≤ 0≤a b≤0) *-left-zero

    *₂-preserves-≤0 : {a b : D} -> a ≤ 0# -> 0# ≤ b -> (a * b) ≤ 0#
    *₂-preserves-≤0 a≤0 0≤b =
      trans-≤-= (*₁-flips-≤ a≤0 0≤b) *-right-zero

    *-flips-≤0 : {a b : D} -> a ≤ 0# -> b ≤ 0# -> 0# ≤ (a * b)
    *-flips-≤0 {a} {b} a≤0 b≤0 = subst (_≤ (a * b)) *-left-zero (*₂-flips-≤ a≤0 b≤0)


module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D}
         (S : Semiring ACM) (LO : isLinearOrder D<) (PO : isPartialOrder D≤) where
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

module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}} {{PO : isPartialOrder D≤}}
         {{SPOS : StronglyPartiallyOrderedSemiringStr S LO PO}} where

  private
    module SPOS = StronglyPartiallyOrderedSemiringStr SPOS

  abstract
    *₁-reflects-≤ : {a b c : D} -> (0# < a) -> (a * b) ≤ (a * c) -> (b ≤ c)
    *₁-reflects-≤ = SPOS.*₁-reflects-≤

    *₂-reflects-≤ : {a b c : D} -> (a * c) ≤ (b * c) -> (0# < c) -> (a ≤ b)
    *₂-reflects-≤ {a} {b} {c} ac≤bc 0<c =
      *₁-reflects-≤ 0<c (subst2 _≤_ *-commute *-commute ac≤bc)

record LinearlyOrderedSemiringʰᵉ
    {ℓ₁ ℓ₂ ℓ<₁ ℓ<₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {<₁ : Rel D₁ ℓ<₁} {<₂ : Rel D₂ ℓ<₂}
    {ACM₁ : AdditiveCommMonoid D₁}
    {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {LO₁ : isLinearOrder <₁} {LO₂ : isLinearOrder <₂}
    (LOS₁ : LinearlyOrderedSemiringStr S₁ LO₁)
    (LOS₂ : LinearlyOrderedSemiringStr S₂ LO₂)
    (f : D₁ -> D₂) : Type (ℓ-max* 4 ℓ₁ ℓ₂ ℓ<₁ ℓ<₂)
    where

  field
    semiringʰ : Semiringʰᵉ S₁ S₂ f
    <ʰ : LinearOrderʰᵉ LO₁ LO₂ f

  open Semiringʰ semiringʰ public
  open LinearOrderʰ <ʰ public

LinearlyOrderedSemiringʰ :
  {ℓ₁ ℓ₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
  {<₁ : Rel D₁ ℓ<₁} {<₂ : Rel D₂ ℓ<₂}
  {ACM₁ : AdditiveCommMonoid D₁}
  {ACM₂ : AdditiveCommMonoid D₂}
  {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
  {LO₁ : isLinearOrder <₁} {LO₂ : isLinearOrder <₂}
  {{LOS₁ : LinearlyOrderedSemiringStr S₁ LO₁}}
  {{LOS₂ : LinearlyOrderedSemiringStr S₂ LO₂}}
  (f : D₁ -> D₂) -> Type (ℓ-max* 4 ℓ₁ ℓ₂ ℓ<₁ ℓ<₂)
LinearlyOrderedSemiringʰ {{LOS₁ = LOS₁}} {{LOS₂ = LOS₂}} f =
  LinearlyOrderedSemiringʰᵉ LOS₁ LOS₂ f

module LinearlyOrderedSemiringʰ
  {ℓ₁ ℓ₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
  {<₁ : Rel D₁ ℓ<₁} {<₂ : Rel D₂ ℓ<₂}
  {ACM₁ : AdditiveCommMonoid D₁}
  {ACM₂ : AdditiveCommMonoid D₂}
  {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
  {LO₁ : isLinearOrder <₁} {LO₂ : isLinearOrder <₂}
  {LOS₁ : LinearlyOrderedSemiringStr S₁ LO₁}
  {LOS₂ : LinearlyOrderedSemiringStr S₂ LO₂}
  {f : D₁ -> D₂} (h : LinearlyOrderedSemiringʰᵉ LOS₁ LOS₂ f) where
  open LinearlyOrderedSemiringʰᵉ h public


module _
    {ℓ₁ ℓ₂ ℓ<₁ ℓ<₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {<₁ : Rel D₁ ℓ<₁} {<₂ : Rel D₂ ℓ<₂}
    {ACM₁ : AdditiveCommMonoid D₁}
    {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {LO₁ : isLinearOrder <₁} {LO₂ : isLinearOrder <₂}
    {LOS₁ : LinearlyOrderedSemiringStr S₁ LO₁}
    {LOS₂ : LinearlyOrderedSemiringStr S₂ LO₂}
    {f : D₁ -> D₂} where
  abstract
    isProp-LinearlyOrderedSemiringʰ : isProp (LinearlyOrderedSemiringʰᵉ LOS₁ LOS₂ f)
    isProp-LinearlyOrderedSemiringʰ h1 h2 i .LinearlyOrderedSemiringʰ.semiringʰ =
      isProp-Semiringʰ (LinearlyOrderedSemiringʰ.semiringʰ h1) (LinearlyOrderedSemiringʰ.semiringʰ h2) i
    isProp-LinearlyOrderedSemiringʰ h1 h2 i .LinearlyOrderedSemiringʰ.<ʰ =
      isProp-LinearOrderʰ (LinearlyOrderedSemiringʰ.<ʰ h1) (LinearlyOrderedSemiringʰ.<ʰ h2) i

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
         (LOS : LinearlyOrderedSemiringStr S LO)
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IS = S

  record NonTrivialLinearlyOrderedSemiringStr : Type (ℓ-max ℓD ℓ<)
    where
    no-eta-equality
    field
      0<1 : 0# < 1#

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{NTS : NonTrivialLinearlyOrderedSemiringStr LOS}}
    where
    open NonTrivialLinearlyOrderedSemiringStr NTS public

    module _ {{LOAS : LinearlyOrderedAdditiveStr ACM LO}} where
      opaque
        0<2 : 0# < 2#
        0<2 = +-preserves-0< 0<1 0<1
