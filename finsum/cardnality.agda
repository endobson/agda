{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.cardnality where

open import additive-group.instances.nat
open import base
open import equality
open import finset
open import nat
open import finsum.arithmetic
open import finsum
open import finset.instances
open import ring.implementations

cardnality-× : {ℓ : Level} (S₁ S₂ : FinSet ℓ) ->
               cardnality (FinSet-× S₁ S₂) == cardnality S₁ *' cardnality S₂
cardnality-× S₁ S₂ =
  cardnality-Σ3 S₁ (\_ -> S₂) >=>
  cong (\x -> (finiteSumᵉ S₁ (\s -> x))) (sym *'-right-one) >=>
  finiteSum-* {k = cardnality S₂} >=>
  cong (cardnality S₂ *'_) (finiteSum'-one {S = S₁}) >=>
  *'-commute {cardnality S₂} {cardnality S₁}
  where
  instance
    FinSetStr-S₁ : FinSetStr (fst S₁)
    FinSetStr-S₁ = record {isFin = snd S₁}
    FinSetStr-S₂ : FinSetStr (fst S₂)
    FinSetStr-S₂ = record {isFin = snd S₂}
