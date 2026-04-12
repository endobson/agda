{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.pushout where

open import base
open import pointed.base
open import pushout

module _ {ℓB ℓC : Level} ((B , ★B) : Type∙ ℓB) ((C , ★C) : Type∙ ℓC) where
  Wedge : Type (ℓ-max ℓB ℓC)
  Wedge = Pushout {A = Top} (\_ -> ★B) (\_ -> ★C)
  Wedge∙ : Type∙ (ℓ-max ℓB ℓC)
  Wedge∙ = Wedge , inj-l ★B

module _ {ℓB ℓC : Level} {B∙@(B , ★B) : Type∙ ℓB} {C∙@(C , ★C) : Type∙ ℓC} where
  Wedge->× : Wedge B∙ C∙ -> B × C
  Wedge->× (inj-l b) = b , ★C
  Wedge->× (inj-r c) = ★B , c
  Wedge->× (glue tt i) = ★B , ★C

module _ {ℓB ℓC : Level} (B∙@(B , ★B) : Type∙ ℓB) (C∙@(C , ★C) : Type∙ ℓC) where
  Smash : Type (ℓ-max ℓB ℓC)
  Smash = Pushout {A = Wedge B∙ C∙} (\_ -> tt) Wedge->×
  Smash∙ : Type∙ (ℓ-max ℓB ℓC)
  Smash∙ = Smash , inj-r (★B , ★C)
