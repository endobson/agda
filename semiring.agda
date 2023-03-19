{-# OPTIONS --cubical --safe --exact-split #-}

module semiring where

open import base
open import additive-group
open import commutative-monoid
open import equality
open import functions
open import hlevel
open import monoid
open import infinity-monoid

private
  variable
    ℓ : Level
    A : Set ℓ

record Semiring {ℓ : Level} {Domain : Type ℓ} (ACM : AdditiveCommMonoid Domain) : Type ℓ where
  no-eta-equality
  infixl 7 _*_

  private
    instance IACM = ACM

  field
    1# : Domain
    _*_ : Domain -> Domain -> Domain
    *-assoc : {m n o : Domain} -> (m * n) * o == m * (n * o)
    *-commute : {m n : Domain} -> (m * n) == (n * m)
    *-left-zero : {m : Domain} -> (0# * m) == 0#
    *-left-one : {m : Domain} -> (1# * m) == m
    *-distrib-+-right : {m n o : Domain} -> (m + n) * o == (m * o) + (n * o)
    isSet-Domain : isSet Domain

  abstract
    *-right-zero : {m : Domain} -> (m * 0#) == 0#
    *-right-zero {m} = (*-commute {m} {0#}) >=> (*-left-zero {m})
    *-right-one : {m : Domain} -> (m * 1#) == m
    *-right-one {m} = (*-commute {m} {1#}) >=> (*-left-one {m})

  instance
    +-CommMonoid : CommMonoid Domain
    +-CommMonoid = AdditiveCommMonoid.comm-monoid ACM

    +-Monoid : Monoid Domain
    +-Monoid = CommMonoid.monoid +-CommMonoid

    +-InfinityMonoid : InfinityMonoid Domain
    +-InfinityMonoid = record
      { ε = 0#
      ; _∙_ = _+_
      ; ∙-assoc = +-assoc
      ; ∙-left-ε = +-left-zero
      ; ∙-right-ε = +-right-zero
      }

    *-CommMonoid : CommMonoid Domain
    *-CommMonoid = record
      { monoid = record
        { ε = 1#
        ; _∙_ = _*_
        ; ∙-assoc = *-assoc
        ; ∙-left-ε = *-left-one
        ; ∙-right-ε = *-right-one
        ; isSet-Domain = isSet-Domain
        }
      ; ∙-commute = *-commute
      }

    *-Monoid : Monoid Domain
    *-Monoid = CommMonoid.monoid *-CommMonoid

    *-InfinityMonoid : InfinityMonoid Domain
    *-InfinityMonoid = record
      { ε = 1#
      ; _∙_ = _*_
      ; ∙-assoc = *-assoc
      ; ∙-left-ε = *-left-one
      ; ∙-right-ε = *-right-one
      }



module _ {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM
    module S = Semiring S

  open Semiring S public using (1# ; _*_)

  abstract
    *-assoc : {m n o : D} -> (m * n) * o == m * (n * o)
    *-assoc = S.*-assoc

    *-commute : {m n : D} -> (m * n) == (n * m)
    *-commute = S.*-commute

    *-left-zero : {m : D} -> (0# * m) == 0#
    *-left-zero = S.*-left-zero

    *-left-one : {m : D} -> (1# * m) == m
    *-left-one = S.*-left-one

    *-distrib-+-right : {m n o : D} -> (m + n) * o == (m * o) + (n * o)
    *-distrib-+-right = S.*-distrib-+-right

    *-right-zero : {m : D} -> (m * 0#) == 0#
    *-right-zero = S.*-right-zero

    *-right-one : {m : D} -> (m * 1#) == m
    *-right-one = S.*-right-one

    *-distrib-+-left : {m n o : D} -> m * (n + o) == (m * n) + (m * o)
    *-distrib-+-left {m} {n} {o} =
      begin
        m * (n + o)
      ==< (*-commute {m} {n + o}) >
        (n + o) * m
      ==< (*-distrib-+-right {n} {o} {m}) >
        n * m + o * m
      ==< (cong2 _+_ (*-commute {n} {m}) (*-commute {o} {m})) >
        (m * n) + (m * o)
      end

    *-right : {m n p : D} -> (n == p) -> m * n == m * p
    *-right {m} id = cong (\x -> m * x) id

    *-left : {m n p : D} -> (n == p) -> n * m == p * m
    *-left {m} id = cong (\x -> x * m) id

    *-cong : {m n p o : D} -> m == p -> n == o -> m * n == p * o
    *-cong = cong2 _*_

    *-swap : {m n o p : D} -> (m * n) * (o * p) == (m * o) * (n * p)
    *-swap = *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc

    -- Explicit versions when implicts don't infer well

    *-left-zeroᵉ : (m : D) -> (0# * m) == 0#
    *-left-zeroᵉ _ = *-left-zero

    *-right-zeroᵉ : (m : D) -> (m * 0#) == 0#
    *-right-zeroᵉ _ = *-right-zero

    *-left-oneᵉ : (m : D) -> (1# * m) == m
    *-left-oneᵉ _ = *-left-one

    *-right-oneᵉ : (m : D) -> (m * 1#) == m
    *-right-oneᵉ _ = *-right-one

    *-distrib-+-rightᵉ : (m n o : D) -> (m + n) * o == (m * o) + (n * o)
    *-distrib-+-rightᵉ _ _ _ = *-distrib-+-right

    *-distrib-+-leftᵉ : (m n o : D) -> m * (n + o) == (m * n) + (m * o)
    *-distrib-+-leftᵉ _ _ _ = *-distrib-+-left

    *-commuteᵉ : (m n : D) -> (m * n) == (n * m)
    *-commuteᵉ _ _ = *-commute

    *-assocᵉ : (m n o : D) -> (m * n) * o == m * (n * o)
    *-assocᵉ _ _ _ = *-assoc



record Semiringʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁}
    {ACM₂ : AdditiveCommMonoid D₂}
    (S₁ : Semiring ACM₁) (S₂ : Semiring ACM₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
    where
  private
    module S₁ = Semiring S₁
    module S₂ = Semiring S₂
    module M+₁ = Monoid S₁.+-Monoid
    module M+₂ = Monoid S₂.+-Monoid
    module M*₁ = Monoid S₁.*-Monoid
    module M*₂ = Monoid S₂.*-Monoid

  field
    +ʰ : monoid.Monoidʰᵉ S₁.+-Monoid S₂.+-Monoid f
    *ʰ : monoid.Monoidʰᵉ S₁.*-Monoid S₂.*-Monoid f

  preserves-0# : f M+₁.ε == M+₂.ε
  preserves-0# = Monoidʰ.preserves-ε +ʰ
  preserves-+ : ∀ x y -> f (x M+₁.∙ y) == (f x) M+₂.∙ (f y)
  preserves-+ = Monoidʰ.preserves-∙ +ʰ
  preserves-1# : f M*₁.ε == M*₂.ε
  preserves-1# = Monoidʰ.preserves-ε *ʰ
  preserves-* : ∀ x y -> f (x M*₁.∙ y) == (f x) M*₂.∙ (f y)
  preserves-* = Monoidʰ.preserves-∙ *ʰ

Semiringʰ :
  {ℓ₁ ℓ₂ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
  {ACM₁ : AdditiveCommMonoid D₁}
  {ACM₂ : AdditiveCommMonoid D₂}
  {{S₁ : Semiring ACM₁}} {{S₂ : Semiring ACM₂}}
  (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Semiringʰ {{S₁ = S₁}} {{S₂ = S₂}} f = Semiringʰᵉ S₁ S₂ f

module Semiringʰ
  {ℓ₁ ℓ₂ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
  {ACM₁ : AdditiveCommMonoid D₁}
  {ACM₂ : AdditiveCommMonoid D₂}
  {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
  {f : D₁ -> D₂} (h : Semiringʰᵉ S₁ S₂ f)
  where
  open Semiringʰᵉ h public

module _
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂}
    {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂}
    {f : D₁ -> D₂}
    where
  abstract
    isProp-Semiringʰ : isProp (Semiringʰᵉ S₁ S₂ f)
    isProp-Semiringʰ h1 h2 i .Semiringʰ.+ʰ =
      isProp-Monoidʰ (Semiringʰ.+ʰ h1) (Semiringʰ.+ʰ h2) i
    isProp-Semiringʰ h1 h2 i .Semiringʰ.*ʰ =
      isProp-Monoidʰ (Semiringʰ.*ʰ h1) (Semiringʰ.*ʰ h2) i


Semiringʰ-∘ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {ACM₁ : AdditiveCommMonoid D₁} {ACM₂ : AdditiveCommMonoid D₂} {ACM₃ : AdditiveCommMonoid D₃}
  {S₁ : Semiring ACM₁} {S₂ : Semiring ACM₂} {S₃ : Semiring ACM₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂} ->
  (Semiringʰᵉ S₂ S₃ f) ->
  (Semiringʰᵉ S₁ S₂ g) ->
  (Semiringʰᵉ S₁ S₃ (f ∘ g))
Semiringʰ-∘ f g = record
  { +ʰ = Monoidʰ-∘ f.+ʰ g.+ʰ
  ; *ʰ = Monoidʰ-∘ f.*ʰ g.*ʰ
  }
  where
  module f = Semiringʰ f
  module g = Semiringʰ g
