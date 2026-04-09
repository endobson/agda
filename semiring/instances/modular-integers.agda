{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.instances.modular-integers where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.modular-integers
open import base
open import equality-path
open import int.base
open import modular-integers
open import ring
open import ring.implementations.int
open import semiring
open import semiring.unit
open import set-quotient

module _ {n : Nat} where
  private
    ℤ/nℤ* : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
    ℤ/nℤ* = SetQuotientElim.rec2 squash/ (\x y -> [ x * y ]) f~₁ f~₂
      where
      opaque
        f~₁ : ∀ (x y z : ℤ) -> ℤ/nℤ~ n x y -> Path (ℤ/nℤ n) [ x * z ] [ y * z ]
        f~₁ x y z (a , p) = eq/ (x * z) (y * z) (z * a , *-assoc >=> *-right p >=> *-commute >=> *-distrib-diff-right)
        f~₂ : ∀ (x y z : ℤ) -> ℤ/nℤ~ n y z -> Path (ℤ/nℤ n) [ x * y ] [ x * z ]
        f~₂ x y z (a , p) = eq/ (x * y) (x * z) (x * a , *-assoc >=> *-right p >=> *-distrib-diff-left)

    opaque
      ℤ/nℤ*-assoc : (x y z : ℤ/nℤ n) -> (ℤ/nℤ* (ℤ/nℤ* x y) z) == (ℤ/nℤ* x (ℤ/nℤ* y z))
      ℤ/nℤ*-assoc =
        SetQuotientElim.elimProp3 (\_ _ _ -> squash/ _ _)
          (\_ _ _ -> cong [_] *-assoc)
      ℤ/nℤ*-commute : (x y : ℤ/nℤ n) -> (ℤ/nℤ* x y) == (ℤ/nℤ* y x)
      ℤ/nℤ*-commute =
        SetQuotientElim.elimProp2 (\_ _ -> squash/ _ _)
          (\_ _ -> cong [_] *-commute)

      ℤ/nℤ*-left-one : (x : ℤ/nℤ n) -> (ℤ/nℤ* [ 1# ] x) == x
      ℤ/nℤ*-left-one =
        SetQuotientElim.elimProp (\_ -> squash/ _ _)
          (\_ -> cong [_] *-left-one)
      ℤ/nℤ*-left-zero : (x : ℤ/nℤ n) -> (ℤ/nℤ* [ 0# ] x) == [ 0# ]
      ℤ/nℤ*-left-zero =
        SetQuotientElim.elimProp (\_ -> squash/ _ _)
          (\_ -> cong [_] *-left-zero)

      ℤ/nℤ*-distrib-+-right : (x y z : ℤ/nℤ n) -> (ℤ/nℤ* (x + y) z) == (ℤ/nℤ* x z + ℤ/nℤ* y z)
      ℤ/nℤ*-distrib-+-right =
        SetQuotientElim.elimProp3 (\_ _ _ -> squash/ _ _)
          (\_ _ _ -> cong [_] *-distrib-+-right)


  instance
    Semiring-ℤ/nℤ : Semiring AdditiveCommMonoid-ℤ/nℤ
    Semiring-ℤ/nℤ = record
      { 1# = [ 1# ]
      ; _*_ = ℤ/nℤ*
      ; *-assoc = \ {x} {y} {z} -> ℤ/nℤ*-assoc x y z
      ; *-commute = \ {x} {y} -> ℤ/nℤ*-commute x y
      ; *-left-zero = \ {x} -> ℤ/nℤ*-left-zero x
      ; *-left-one = ℤ/nℤ*-left-one _
      ; *-distrib-+-right = \ {x} {y} {z} -> ℤ/nℤ*-distrib-+-right x y z
      ; isSet-Domain = isSet-ℤ/nℤ
      }

ℤ/nℤˣ : (n : Nat) -> Type₀
ℤ/nℤˣ n = Unit (ℤ/nℤ n)
