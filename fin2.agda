{-# OPTIONS --cubical --safe --exact-split #-}

module fin2 where

open import base
open import sum

Fin : Nat -> Type₀
Fin zero = Bot
Fin (suc n) = Top ⊎ Fin n

zero-fin : (n : Nat) -> Fin (suc n)
zero-fin _ = inj-l tt

max-fin : (n : Nat) -> Fin (suc n)
max-fin zero = (inj-l tt)
max-fin (suc n) = inj-r (max-fin n)
