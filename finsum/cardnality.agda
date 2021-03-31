{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.cardnality where

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
  cong (\x -> (finiteSum S₁ (\s -> x))) (sym *'-right-one) >=>
  finiteSum-* {k = cardnality S₂} >=>
  cong (cardnality S₂ *'_) (finiteSum'-one {S = S₁}) >=>
  *'-commute {cardnality S₂} {cardnality S₁}
