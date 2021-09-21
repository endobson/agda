{-# OPTIONS --cubical --safe --exact-split #-}

module semiring where

open import base
open import additive-group using (AdditiveCommMonoid)
open import commutative-monoid
open import equality
open import hlevel
open import monoid
open import sign

private
  variable
    ℓ : Level
    A : Set ℓ

record Semiring {ℓ : Level} (Domain : Type ℓ) {{ACM : AdditiveCommMonoid Domain}} : Type ℓ where
  no-eta-equality
  infixl 7 _*_
  infixl 6 _+_

  field
    0# : Domain
    1# : Domain
    _+_ : Domain -> Domain -> Domain
    _*_ : Domain -> Domain -> Domain
    +-assoc : {m n o : Domain} -> (m + n) + o == m + (n + o)
    +-commute : {m n : Domain} -> (m + n) == (n + m)
    *-assoc : {m n o : Domain} -> (m * n) * o == m * (n * o)
    *-commute : {m n : Domain} -> (m * n) == (n * m)
    +-left-zero : {m : Domain} -> (0# + m) == m
    *-left-zero : {m : Domain} -> (0# * m) == 0#
    *-left-one : {m : Domain} -> (1# * m) == m
    *-distrib-+-right : {m n o : Domain} -> (m + n) * o == (m * o) + (n * o)
    isSet-Domain : isSet Domain

  +-right-zero : {m : Domain} -> (m + 0#) == m
  +-right-zero {m} = (+-commute {m} {0#}) >=> (+-left-zero {m})

  *-right-zero : {m : Domain} -> (m * 0#) == 0#
  *-right-zero {m} = (*-commute {m} {0#}) >=> (*-left-zero {m})
  *-right-one : {m : Domain} -> (m * 1#) == m
  *-right-one {m} = (*-commute {m} {1#}) >=> (*-left-one {m})

  instance
    +-Monoid : Monoid Domain
    +-Monoid = record
      { ε = 0#
      ; _∙_ = _+_
      ; ∙-assoc = (\ {m} {n} {o} -> +-assoc {m} {n} {o})
      ; ∙-left-ε = (\ {m} -> +-left-zero {m})
      ; ∙-right-ε = (\ {m} -> +-right-zero {m})
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
      ; ∙-assoc = (\ {m} {n} {o} -> *-assoc {m} {n} {o})
      ; ∙-left-ε = (\ {m} -> *-left-one {m})
      ; ∙-right-ε = (\ {m} -> *-right-one {m})
      }

    *-CommMonoid : CommMonoid Domain
    *-CommMonoid = record
      { ∙-commute = *-commute
      ; isSet-Domain = isSet-Domain
      }


  *-distrib-+-left : {m n o : Domain} -> m * (n + o) == (m * n) + (m * o)
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


  +-right : {m n p : Domain} -> (n == p) -> m + n == m + p
  +-right {m} id = cong (\x -> m + x) id

  +-left : {m n p : Domain} -> (n == p) -> n + m == p + m
  +-left {m} id = cong (\x -> x + m) id

  +-cong : {m n p o : Domain} -> m == p -> n == o -> m + n == p + o
  +-cong = cong2 _+_

  *-right : {m n p : Domain} -> (n == p) -> m * n == m * p
  *-right {m} id = cong (\x -> m * x) id

  *-left : {m n p : Domain} -> (n == p) -> n * m == p * m
  *-left {m} id = cong (\x -> x * m) id

  *-cong : {m n p o : Domain} -> m == p -> n == o -> m * n == p * o
  *-cong = cong2 _*_


  +-swap : {m n o p : Domain} -> (m + n) + (o + p) == (m + o) + (n + p)
  +-swap = +-assoc >=> +-right (sym +-assoc >=> +-left +-commute >=> +-assoc) >=> sym +-assoc


module _ {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} {{S : Semiring D}} where
  open Semiring S public


--record SignedSemiringStr {ℓD : Level} (D : Type ℓD) (ℓS : Level) : Type (ℓ-max ℓD (ℓ-suc ℓS)) where
--  field
--    {{ semiring }} : Semiring D
--    {{ sign }} : SignStr D ℓS
--
--  field
--    Zero-0# : Zero 0#
--    Pos-1# : Pos 1#


--   open Semiring semiring
--   open SignStr sign
--
--   field
--     Zero-0# : Zero 0#
--     Pos-1# : Pos 1#
--     +-Pos-Pos : {x y : D} -> Pos x -> Pos y -> Pos (x + y)
--     +-Neg-Neg : {x y : D} -> Neg x -> Neg y -> Neg (x + y)
--     *-Pos-Pos : {x y : D} -> Pos x -> Pos y -> Pos (x * y)
