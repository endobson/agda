{-# OPTIONS --cubical --safe --exact-split #-}

module semiring where

open import base
open import additive-group
open import commutative-monoid
open import equality
open import hlevel
open import monoid
open import sign

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
    +-Monoid : Monoid Domain
    +-Monoid = record
      { ε = 0#
      ; _∙_ = _+_
      ; ∙-assoc = +-assoc
      ; ∙-left-ε = +-left-zero
      ; ∙-right-ε = +-right-zero
      }

    +-CommMonoid : CommMonoid Domain
    +-CommMonoid = record
      { ∙-commute = +-commute
      ; isSet-Domain = isSet-Domain
      }

    *-Monoid : Monoid Domain
    *-Monoid = record
      { ε = 1#
      ; _∙_ = _*_
      ; ∙-assoc = *-assoc
      ; ∙-left-ε = *-left-one
      ; ∙-right-ε = *-right-one
      }

    *-CommMonoid : CommMonoid Domain
    *-CommMonoid = record
      { ∙-commute = *-commute
      ; isSet-Domain = isSet-Domain
      }



module _ {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  open Semiring S public using (1# ; _*_)

  abstract
    open Semiring S public using
      ( *-assoc
      ; *-commute
      ; *-left-zero
      ; *-right-zero
      ; *-left-one
      ; *-right-one
      ; *-distrib-+-right
      )


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


    +-right : {m n p : D} -> (n == p) -> m + n == m + p
    +-right {m} id = cong (\x -> m + x) id

    +-left : {m n p : D} -> (n == p) -> n + m == p + m
    +-left {m} id = cong (\x -> x + m) id

    +-cong : {m n p o : D} -> m == p -> n == o -> m + n == p + o
    +-cong = cong2 _+_

    *-right : {m n p : D} -> (n == p) -> m * n == m * p
    *-right {m} id = cong (\x -> m * x) id

    *-left : {m n p : D} -> (n == p) -> n * m == p * m
    *-left {m} id = cong (\x -> x * m) id

    *-cong : {m n p o : D} -> m == p -> n == o -> m * n == p * o
    *-cong = cong2 _*_


    +-swap : {m n o p : D} -> (m + n) + (o + p) == (m + o) + (n + p)
    +-swap = +-assoc >=> +-right (sym +-assoc >=> +-left +-commute >=> +-assoc) >=> sym +-assoc
