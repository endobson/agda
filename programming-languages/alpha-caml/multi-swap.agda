{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml.multi-swap where

open import base
open import list
open import programming-languages.alpha-caml
open import programming-languages.alpha-caml.single-swap

multi-swap-term : List (Atom × Atom) -> Term -> Term
multi-swap-term [] t = t
multi-swap-term (p :: ps) t = single-swap-term p (multi-swap-term ps t)
