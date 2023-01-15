{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.cardinality where

open import additive-group.instances.nat
open import base
open import equality
open import finset
open import nat
open import finsum.arithmetic
open import finsum
open import finset.instances
open import semiring.instances.nat

cardinality-× : {ℓ : Level} (S₁ S₂ : FinSet ℓ) ->
                cardinality (FinSet-× S₁ S₂) == cardinality S₁ *' cardinality S₂
cardinality-× S₁ S₂ =
  cardinality-Σ3 S₁ (\_ -> S₂) >=>
  cong (\x -> (finiteSumᵉ S₁ (\s -> x))) (sym *'-right-one) >=>
  finiteSum-* {k = cardinality S₂} >=>
  cong (cardinality S₂ *'_) (finiteSum'-one {S = S₁}) >=>
  *'-commute {cardinality S₂} {cardinality S₁}
  where
  instance
    FinSetStr-S₁ : FinSetStr (fst S₁)
    FinSetStr-S₁ = record {isFin = snd S₁}
    FinSetStr-S₂ : FinSetStr (fst S₂)
    FinSetStr-S₂ = record {isFin = snd S₂}
