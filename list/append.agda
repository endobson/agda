{-# OPTIONS --cubical --safe --exact-split #-}

module list.append where

open import base
open import equality
open import list.base

private
  variable
    ℓ : Level
    A : Type ℓ

++-assoc : {a : List A} {b : List A} {c : List A} -> (a ++ b) ++ c == a ++ (b ++ c)
++-assoc {a = []} {b} {c} = refl
++-assoc {a = a :: as} {b} {c} = cong (a ::_) (++-assoc {a = as} {b} {c})

++-left-[] : {as : List A} -> ([] ++ as) == as
++-left-[] = refl

++-right-[] : {as : List A} -> (as ++ []) == as
++-right-[] {as = []} = refl
++-right-[] {as = a :: as} = cong (a ::_) (++-right-[] {as = as})
