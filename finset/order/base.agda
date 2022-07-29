{-# OPTIONS --cubical --safe --exact-split #-}

module finset.order.base where

open import base
open import finset
open import nat.order

FinSet≤ : {ℓA ℓB : Level} -> (A : FinSet ℓA) -> (B : FinSet ℓB) -> Type₀
FinSet≤ A B = cardinality A ≤ cardinality B

FinSet< : {ℓA ℓB : Level} -> (A : FinSet ℓA) -> (B : FinSet ℓB) -> Type₀
FinSet< A B = cardinality A < cardinality B

FinSetⁱ< : {ℓA ℓB : Level} -> (A : Type ℓA) -> (B : Type ℓB) -> 
           {{fsA : FinSetStr A}} {{fsB : FinSetStr B}} -> Type₀
FinSetⁱ< A B = cardinalityⁱ A < cardinalityⁱ B

FinSetⁱ≤ : {ℓA ℓB : Level} -> (A : Type ℓA) -> (B : Type ℓB) -> 
           {{fsA : FinSetStr A}} {{fsB : FinSetStr B}} -> Type₀
FinSetⁱ≤ A B = cardinalityⁱ A ≤ cardinalityⁱ B
