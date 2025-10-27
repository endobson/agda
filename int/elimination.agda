{-# OPTIONS --cubical --safe --exact-split #-}

module int.elimination where

open import base
open import int.add1
open import int.base

-- Elimination procedures

IntElim-add1sub1-elim : {ℓ : Level} {P : Int -> Type ℓ}
                        (f-z : P zero-int)
                        (f-add1 : (n : Int) -> P n -> P (add1 n))
                        (f-sub1 : (n : Int) -> P n -> P (sub1 n))
                        (n : Int) -> P n
IntElim-add1sub1-elim f-z f-add1 f-sub1 (nonneg zero) = f-z
IntElim-add1sub1-elim f-z f-add1 f-sub1 (nonneg (suc n)) =
  f-add1 (nonneg n) (IntElim-add1sub1-elim f-z f-add1 f-sub1 (nonneg n))
IntElim-add1sub1-elim f-z f-add1 f-sub1 (neg zero) = f-sub1 (int 0) f-z
IntElim-add1sub1-elim f-z f-add1 f-sub1 (neg (suc n)) =
  f-sub1 (neg n) (IntElim-add1sub1-elim f-z f-add1 f-sub1 (neg n))

IntElim-add1minus-elim : {ℓ : Level} {P : Int -> Type ℓ}
                         (f-z : P zero-int)
                         (f-add1 : (n : Int) -> P n -> P (add1 n))
                         (f-minus : (n : Int) -> P n -> P (ℤ- n))
                         (n : Int) -> P n
IntElim-add1minus-elim f-z f-add1 f-minus (nonneg zero) = f-z
IntElim-add1minus-elim f-z f-add1 f-minus (nonneg (suc n)) =
  f-add1 (nonneg n) (IntElim-add1minus-elim f-z f-add1 f-minus (nonneg n))
IntElim-add1minus-elim f-z f-add1 f-minus (neg zero) =
  f-minus _ (f-add1 (int 0) f-z)
IntElim-add1minus-elim f-z f-add1 f-minus (neg (suc n)) =
  f-minus _ (f-add1 _ (f-minus _ (IntElim-add1minus-elim f-z f-add1 f-minus (neg n))))

IntElim-sucminus-elim : {ℓ : Level} {P : Int -> Type ℓ}
                        (f-z : P zero-int)
                        (f-suc : (n : Nat) -> P (int n) -> P (int (suc n)))
                        (f-minus : (n : Int) -> P n -> P (ℤ- n))
                        (n : Int) -> P n
IntElim-sucminus-elim f-z f-suc f-minus (nonneg zero) = f-z
IntElim-sucminus-elim f-z f-suc f-minus (nonneg (suc n)) =
  f-suc n (IntElim-sucminus-elim f-z f-suc f-minus (nonneg n))
IntElim-sucminus-elim f-z f-suc f-minus (neg zero) =
  f-minus _ (f-suc 0 f-z)
IntElim-sucminus-elim f-z f-suc f-minus (neg (suc n)) =
  f-minus _ (f-suc _ (f-minus _ (IntElim-sucminus-elim f-z f-suc f-minus (neg n))))

IntElim-ℕminus-elim : {ℓ : Level} {P : Int -> Type ℓ}
                      (f-ℕ : (n : Nat) -> P (int n))
                      (f-minus : (n : Int) -> P n -> P (ℤ- n))
                      (n : Int) -> P n
IntElim-ℕminus-elim f-ℕ f-minus (nonneg n) = f-ℕ n
IntElim-ℕminus-elim f-ℕ f-minus (neg n) = (f-minus _ (f-ℕ (suc n)))

IntElim-ℕminus'-elim : {ℓ : Level} {P : Int -> Type ℓ}
                       (f-ℕ : (n : Nat) -> P (int n))
                       (f-minus : (n : Nat) -> P (int n) -> P (ℤ- (int n)))
                       (n : Int) -> P n
IntElim-ℕminus'-elim f-ℕ f-minus (nonneg n) = f-ℕ n
IntElim-ℕminus'-elim f-ℕ f-minus (neg n) = (f-minus _ (f-ℕ (suc n)))
