{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.group where

open import additive-group
open import base
open import equality
open import order
open import ordered-additive-group
open import relation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {{O : isLinearOrder D<}} where
  private
    instance
      IACM = ACM

  LinearlyOrderedAdditiveStr-Group :
    (+₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)) ->
    LinearlyOrderedAdditiveStr ACM O
  LinearlyOrderedAdditiveStr-Group +₁-preserves-< = record
    { +₁-preserves-< = +₁-preserves-<
    ; +₁-reflects-< = +₁-reflects-<'
    }
    where
    +₁-reflects-<' : {a b c : D} -> (a + b) < (a + c) -> (b < c)
    +₁-reflects-<' {a} ab<ac = subst2 _<_ p p (+₁-preserves-< ab<ac)
      where
      p : {x : D} -> (- a + (a + x)) == x
      p = sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero
