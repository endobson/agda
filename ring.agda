{-# OPTIONS --cubical --safe --exact-split #-}

module ring where

open import additive-group
open import base
open import commutative-monoid
open import equality
open import functions
open import group
open import hlevel
open import monoid
open import sigma.base
open import semiring

open EqReasoning

private
  variable
    ℓ : Level
    A : Set ℓ

record Ring {ℓ : Level} {Domain : Type ℓ} {ACM : AdditiveCommMonoid Domain}
            (S : Semiring ACM) (AG : AdditiveGroup ACM) : Type ℓ where
  no-eta-equality
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S

  semiring = S

  *-left-minus-one : {a : Domain} -> (- 1#) * a == - a
  *-left-minus-one {a} =
    begin
      - 1# * a
    ==< sym +-left-zero >
      0# + - 1# * a
    ==< +-left (sym +-inverse) >
      (a + - a) + - 1# * a
    ==< +-left +-commute >
      (- a + a) + - 1# * a
    ==< +-assoc >
      - a + (a + - 1# * a)
    ==< +-right (+-left (sym *-left-one)) >
      - a + (1# * a + - 1# * a)
    ==< +-right (sym *-distrib-+-right) >
      - a + ((1# + - 1#) * a)
    ==< +-right (*-left +-inverse) >
      - a + (0# * a)
    ==< +-right *-left-zero >
      - a + 0#
    ==< +-right-zero >
      - a
    end

  minus-extract-left : {a b : Domain} -> (- a * b) == - (a * b)
  minus-extract-left {a} {b} =
    begin
      - a * b
    ==< *-left (sym *-left-minus-one) >
      (- 1# * a) * b
    ==< *-assoc >
      - 1# * (a * b)
    ==< *-left-minus-one >
      - (a * b)
    end
  minus-extract-right : {a b : Domain} -> (a * - b) == - (a * b)
  minus-extract-right = *-commute >=> minus-extract-left >=> cong -_ *-commute

  minus-extract-both : {a b : Domain} -> (- a * - b) == (a * b)
  minus-extract-both = minus-extract-left >=> cong -_ minus-extract-right >=> minus-double-inverse


  +-Group : GroupStr Domain
  +-Group = AdditiveGroup.group-str AG
  +-AbGroup : AbGroupStr Domain
  +-AbGroup = AdditiveGroup.ab-group-str AG


module _ {ℓ : Level} (D : Type ℓ) {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}} {{R : Ring S AG}} where
  Ringⁱ : Ring S AG
  Ringⁱ = R


module _ {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}}
         where
  private
    instance
      IACM = ACM
    R : Ring S AG
    R = record {}
    module R = Ring R

  abstract
    minus-extract-left : {a b : D} -> (- a * b) == - (a * b)
    minus-extract-left = R.minus-extract-left
    minus-extract-right : {a b : D} -> (a * - b) == - (a * b)
    minus-extract-right = R.minus-extract-right
    minus-extract-both : {a b : D} -> (- a * - b) == (a * b)
    minus-extract-both = R.minus-extract-both
    *-left-minus-one : {a : D} -> (- 1#) * a == - a
    *-left-minus-one = R.*-left-minus-one


  abstract
    *-distrib-diff-left : {x y z : D} -> x * (diff y z) == diff (x * y) (x * z)
    *-distrib-diff-left = *-distrib-+-left >=> +-right minus-extract-right

    *-distrib-diff-right : {x y z : D} -> (diff x y) * z == diff (x * z) (y * z)
    *-distrib-diff-right = *-distrib-+-right >=> +-right minus-extract-left

  opaque
    a+b*a-b-path : ∀ {a b : D} -> (a + b) * (a + (- b)) == (a * a + - (b * b))
    a+b*a-b-path =
      *-distrib-+-right >=>
      +-cong *-distrib-+-left (*-distrib-+-left >=> +-commute) >=>
      +-swap >=>
      +-right (+-cong minus-extract-right *-commute >=> +-commute >=> +-inverse) >=>
      +-right-zero >=>
      +-right minus-extract-right


module _
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {AG₁ : AdditiveGroup ACM₁} {AG₂ : AdditiveGroup ACM₂}
    (R₁ : Ring S₁ AG₁) (R₂ : Ring S₂ AG₂)
    (f : D₁ -> D₂) where
  private
    instance
      IACM₁ = ACM₁
      IACM₂ = ACM₂
      IAG₁ = AG₁
      IAG₂ = AG₂

    module R₁ = Ring R₁
    module R₂ = Ring R₂

    module S₁ = Semiring S₁
    module S₂ = Semiring S₂

  record Ringʰᵉ : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      preserves-0# : f 0# == 0#
      preserves-1# : f S₁.1# == S₂.1#
      preserves-+ : ∀ x y -> f (x + y) == f x + f y
      preserves-* : ∀ x y -> f (x S₁.* y) == f x S₂.* f y
      preserves-minus : ∀ x -> f (- x) == - (f x)

    +ʰ : Monoidʰᵉ S₁.+-Monoid S₂.+-Monoid f
    +ʰ = record { preserves-ε = preserves-0# ; preserves-∙ = preserves-+ }
    *ʰ : Monoidʰᵉ S₁.*-Monoid S₂.*-Monoid f
    *ʰ = record { preserves-ε = preserves-1# ; preserves-∙ = preserves-* }

    semiringʰ : Semiringʰᵉ S₁ S₂ f
    semiringʰ = record { +ʰ = +ʰ ; *ʰ = *ʰ }


Ringʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {AG₁ : AdditiveGroup ACM₁} {AG₂ : AdditiveGroup ACM₂}
    {{R₁ : Ring S₁ AG₁}} {{R₂ : Ring S₂ AG₂}}
    (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Ringʰ {{R₁ = R₁}} {{R₂ = R₂}} f = Ringʰᵉ R₁ R₂ f

module Ringʰ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {AG₁ : AdditiveGroup ACM₁} {AG₂ : AdditiveGroup ACM₂}
    {R₁ : Ring S₁ AG₁} {R₂ : Ring S₂ AG₂}
    {f : D₁ -> D₂}
    (s : Ringʰᵉ R₁ R₂ f) where
  open Ringʰᵉ s public

module _
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {AG₁ : AdditiveGroup ACM₁} {AG₂ : AdditiveGroup ACM₂}
    {{R₁ : Ring S₁ AG₁}} {{R₂ : Ring S₂ AG₂}}
    {f : D₁ -> D₂}

    where
  private
    instance
      IACM₁ = ACM₁
      IACM₂ = ACM₂
      IS₁ = S₁
      IS₂ = S₂

    isSetD = AdditiveCommMonoid.isSet-Domain ACM₂

  isProp-Ringʰ : isProp (Ringʰ f)
  isProp-Ringʰ h1 h2 i .Ringʰ.preserves-0# =
    isSetD _ _ (Ringʰ.preserves-0# h1) (Ringʰ.preserves-0# h2) i
  isProp-Ringʰ h1 h2 i .Ringʰ.preserves-1# =
    isSetD _ _ (Ringʰ.preserves-1# h1) (Ringʰ.preserves-1# h2) i
  isProp-Ringʰ h1 h2 i .Ringʰ.preserves-+ x y =
    isSetD _ _ (Ringʰ.preserves-+ h1 x y) (Ringʰ.preserves-+ h2 x y) i
  isProp-Ringʰ h1 h2 i .Ringʰ.preserves-* x y =
    isSetD _ _ (Ringʰ.preserves-* h1 x y) (Ringʰ.preserves-* h2 x y) i
  isProp-Ringʰ h1 h2 i .Ringʰ.preserves-minus x =
    isSetD _ _ (Ringʰ.preserves-minus h1 x) (Ringʰ.preserves-minus h2 x) i

module _
    {ℓ : Level}
    {D : Type ℓ}
    {ACM : AdditiveCommMonoid D}
    {S : Semiring ACM}
    {AG : AdditiveGroup ACM}
    {{R : Ring S AG}} where
  Ringʰ-idFun : Ringʰᵉ R R (\x -> x)
  Ringʰ-idFun = record
    { preserves-0# = refl
    ; preserves-1# = refl
    ; preserves-+ = \_ _ -> refl
    ; preserves-* = \_ _ -> refl
    ; preserves-minus = \_ -> refl
    }
