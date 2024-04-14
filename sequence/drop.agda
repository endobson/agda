{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.drop where

open import base
open import nat
open import sequence
open import functions
open import equality

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

  drop-suc : (m : ℕ) (s : Seq) -> (drop (suc m) s) == drop m (s ∘ suc)
  drop-suc zero    s = refl
  drop-suc (suc n) s = cong (_∘ suc) (drop-suc n s)

  drop-+ : (m n : ℕ) (s : Seq) -> (drop m s n) == s (m +' n)
  drop-+ zero    n s = refl
  drop-+ (suc m) n s = (drop-+ m (suc n) s) >=> cong s +'-right-suc
