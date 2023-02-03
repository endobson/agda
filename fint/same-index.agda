{-# OPTIONS --cubical --safe --exact-split #-}

module fint.same-index where

open import base
open import fin-algebra
open import equality

SameIndex : {n1 n2 : Nat} -> FinT n1 -> FinT n2 -> Type₀
SameIndex {zero}           ()
SameIndex {suc n1} {zero}   _ ()
SameIndex {suc n1} {suc n2} (inj-l _) (inj-l _) = Top
SameIndex {suc n1} {suc n2} (inj-l _) (inj-r _) = Bot
SameIndex {suc n1} {suc n2} (inj-r _) (inj-l _) = Bot
SameIndex {suc n1} {suc n2} (inj-r i) (inj-r j) = SameIndex i j

SameIndex-path : {n : Nat} (i j : FinT n) -> SameIndex i j -> i == j
SameIndex-path {zero} ()
SameIndex-path {suc n} (inj-l _) (inj-l _) _ = refl
SameIndex-path {suc n} (inj-r i) (inj-r j) s = cong inj-r (SameIndex-path i j s)


SameIndex-refl : {n : Nat} (i : FinT n) -> SameIndex i i
SameIndex-refl {zero} ()
SameIndex-refl {suc n} (inj-l _) = tt
SameIndex-refl {suc n} (inj-r i) = (SameIndex-refl i)

trans-SameIndex : {n1 n2 n3 : Nat} {i : FinT n1} {j : FinT n2} {k : FinT n3} ->
                  SameIndex i j -> SameIndex j k -> SameIndex i k
trans-SameIndex {zero}                     {i = ()}
trans-SameIndex {suc n1} {zero}            {j = ()}
trans-SameIndex {suc n1} {suc n2} {zero}   {k = ()}
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-l _} {inj-l _} {inj-l _} _ _ = tt
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-l _} {inj-l _} {inj-r _} _ ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-l _} {inj-r _} {inj-l _} ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-l _} {inj-r _} {inj-r _} ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-r _} {inj-l _} {inj-l _} ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-r _} {inj-l _} {inj-r _} ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-r _} {inj-r _} {inj-l _} _ ()
trans-SameIndex {suc n1} {suc n2} {suc n3} {inj-r i} {inj-r j} {inj-r k} =
  trans-SameIndex {i = i} {j = j} {k = k}
