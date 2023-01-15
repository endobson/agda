{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.decidable where

open import additive-group
open import base
open import equality
open import order
open import ordered-semiring
open import semiring

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM}
         {O : LinearOrderStr D ℓ<} {{LOS : LinearlyOrderedSemiringStr S O}}
         {{DLO : DecidableLinearOrderStr O}} where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  StronglyLinearlyOrderedSemiringStr-Dec< : StronglyLinearlyOrderedSemiringStr S O
  StronglyLinearlyOrderedSemiringStr-Dec< = record
    { +₁-reflects-< = \ab<ac -> stable-< (+₁-reflects-<' ab<ac)
    ; *₁-reflects-< = \ 0<a ab<ac -> stable-< (*₁-reflects-<' 0<a ab<ac)
    }
    where
    +₁-reflects-<' : {a b c : D} -> (a + b) < (a + c) -> ¬ (¬ (b < c))
    +₁-reflects-<' {a} {b} {c} ab<ac b≮c = irrefl-path-< (cong (a +_) b=c) ab<ac
      where
      c≮b : c ≮ b
      c≮b c<b = asym-< ab<ac (+₁-preserves-< c<b)
      b=c : b == c
      b=c = connected-< b≮c c≮b

    *₁-reflects-<' : {a b c : D} -> (0# < a) -> (a * b) < (a * c) -> ¬ (¬ (b < c))
    *₁-reflects-<' {a} {b} {c} 0<a ab<ac b≮c = irrefl-path-< (cong (a *_) b=c) ab<ac
      where
      c≮b : c ≮ b
      c≮b c<b = asym-< ab<ac (*₁-preserves-< 0<a c<b)
      b=c : b == c
      b=c = connected-< b≮c c≮b
