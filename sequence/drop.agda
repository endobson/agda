{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.drop where

open import base
open import nat
open import sequence

private
  variable
    ℓ : Level

module _ {D : Type ℓ} where
  private
    Seq : Type ℓ
    Seq = Sequence D

  drop : ℕ -> Seq -> Seq
  drop zero    s = s
  drop (suc n) s = drop1 (drop n s)
