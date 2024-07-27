{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.properties.binomial-coefficients-factorial where

open import additive-group
open import additive-group.instances.nat
open import base
open import combinatorics.binomial-coefficients
open import combinatorics.factorial
open import equality
open import nat
open import semiring
open import semiring.instances.nat

opaque
  -- (a + b) C a * a! * b! == (a + b)!
  binomial-coeff'-factorial-path : (a b : Nat) ->
    binomial-coeff' a b * (factorial a * factorial b) == factorial (a + b)
  binomial-coeff'-factorial-path zero b = *-left-one >=> *-left-one
  binomial-coeff'-factorial-path (suc a) zero =
    *-left-one >=> *-right-one >=> cong factorial (sym (+-right-zeroᵉ (suc a)))
  binomial-coeff'-factorial-path (suc a) (suc b) =
    *-distrib-+-rightᵉ (binomial-coeff' a (suc b)) (binomial-coeff' (suc a) b)
                       (factorial (suc a) * (factorial (suc b))) >=>
    +-cong p1 p2 >=>
    sym (*-distrib-+-rightᵉ (suc a) (suc b) (factorial (a + suc b)))
    where
    p1 : binomial-coeff' a (suc b) * (factorial (suc a) * factorial (suc b)) ==
        (suc a) * factorial (a + suc b)
    p1 = *-cong (reflᵉ (binomial-coeff' a (suc b)))
                (*-assocᵉ (suc a) (factorial a) (factorial (suc b)) >=>
                 *-commuteᵉ (suc a) (factorial a * factorial (suc b))) >=>
         sym (*-assocᵉ (binomial-coeff' a (suc b)) (factorial a * factorial (suc b)) (suc a)) >=>
         *-left (binomial-coeff'-factorial-path a (suc b)) >=>
         *-commuteᵉ (factorial (a + suc b)) (suc a)
    p2 : binomial-coeff' (suc a) b * (factorial (suc a) * factorial (suc b)) ==
        (suc b) * factorial (a + suc b)
    p2 = *-cong (reflᵉ (binomial-coeff' (suc a) b))
                (*-cong (reflᵉ (factorial (suc a))) (*-commuteᵉ (suc b) (factorial b)) >=>
                 sym (*-assocᵉ (factorial (suc a)) (factorial b) (suc b))) >=>
         sym (*-assocᵉ (binomial-coeff' (suc a) b) (factorial (suc a) * factorial b) (suc b)) >=>
         *-left (binomial-coeff'-factorial-path (suc a) b >=>
                 cong factorial (sym (+'-right-suc {a} {b}))) >=>
         *-commuteᵉ (factorial (a + suc b)) (suc b)
