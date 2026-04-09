{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.modular-integers where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int.base
open import modular-integers
open import ring
open import ring.implementations.int
open import set-quotient

module _ {n : Nat} where
  private
    ℤ/nℤ+ : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
    ℤ/nℤ+ = SetQuotientElim.rec2 squash/ (\x y -> [ x + y ]) f~₁ f~₂
      where
      opaque
        f~₁ : ∀ (x y z : ℤ) -> ℤ/nℤ~ n x y -> Path (ℤ/nℤ n) [ x + z ] [ y + z ]
        f~₁ x y z (a , p) = eq/ (x + z) (y + z) (a , p >=> +₂-preserves-diff)
        f~₂ : ∀ (x y z : ℤ) -> ℤ/nℤ~ n y z -> Path (ℤ/nℤ n) [ x + y ] [ x + z ]
        f~₂ x y z (a , p) = eq/ (x + y) (x + z) (a , p >=> +₁-preserves-diff)

    ℤ/nℤ- : ℤ/nℤ n -> ℤ/nℤ n
    ℤ/nℤ- = SetQuotientElim.rec squash/ (\x -> [ - x ]) f~
      where
      opaque
        f~ : ∀ (x y : ℤ) -> ℤ/nℤ~ n x y -> Path (ℤ/nℤ n) [ - x ] [ - y ]
        f~ x y (a , p) = eq/ (- x) (- y) (- a , minus-extract-left >=> cong -_ p >=> minus-distrib-plus)

    opaque
      ℤ/nℤ+-assoc : (x y z : ℤ/nℤ n) -> (ℤ/nℤ+ (ℤ/nℤ+ x y) z) == (ℤ/nℤ+ x (ℤ/nℤ+ y z))
      ℤ/nℤ+-assoc =
        SetQuotientElim.elimProp3 (\_ _ _ -> squash/ _ _)
          (\_ _ _ -> cong [_] +-assoc)
      ℤ/nℤ+-commute : (x y : ℤ/nℤ n) -> (ℤ/nℤ+ x y) == (ℤ/nℤ+ y x)
      ℤ/nℤ+-commute =
        SetQuotientElim.elimProp2 (\_ _ -> squash/ _ _)
          (\_ _ -> cong [_] +-commute)


      ℤ/nℤ+-left-zero : (x : ℤ/nℤ n) -> (ℤ/nℤ+ [ int 0 ] x) == x
      ℤ/nℤ+-left-zero =
        SetQuotientElim.elimProp (\_ -> squash/ _ _)
          (\_ -> cong [_] +-left-zero)
      ℤ/nℤ+-right-zero : (x : ℤ/nℤ n) -> (ℤ/nℤ+ x [ int 0 ]) == x
      ℤ/nℤ+-right-zero =
        SetQuotientElim.elimProp (\_ -> squash/ _ _)
          (\_ -> cong [_] +-right-zero)

      ℤ/nℤ-+-inverse : (x : ℤ/nℤ n) -> (ℤ/nℤ+ x (ℤ/nℤ- x)) == [ int 0 ]
      ℤ/nℤ-+-inverse =
        SetQuotientElim.elimProp (\_ -> squash/ _ _)
          (\_ -> cong [_] +-inverse)


  instance
    AdditiveCommMonoid-ℤ/nℤ : AdditiveCommMonoid (ℤ/nℤ n)
    AdditiveCommMonoid-ℤ/nℤ = record
      { comm-monoid = record
        { monoid = record
          { ε = [ (int 0) ]
          ; _∙_ = ℤ/nℤ+
          ; ∙-assoc = \{x} {y} {z} -> ℤ/nℤ+-assoc x y z
          ; ∙-left-ε = ℤ/nℤ+-left-zero _
          ; ∙-right-ε = ℤ/nℤ+-right-zero _
          ; isSet-Domain = squash/
          }
        ; ∙-commute = \{x} {y} -> ℤ/nℤ+-commute x y
        }
      }

    AdditiveGroup-ℤ/nℤ : AdditiveGroup AdditiveCommMonoid-ℤ/nℤ
    AdditiveGroup-ℤ/nℤ = record
      { -_ = ℤ/nℤ-
      ; +-inverse = \{x} -> ℤ/nℤ-+-inverse x
      }
