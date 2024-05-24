{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.containment where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-semiring
open import ordered-semiring.minmax
open import rational
open import rational.open-interval
open import rational.open-interval.multiplication-inclusion
open import rational.order
open import relation
open import semiring
open import ring
open import sum
open import sign
open import sign.instances.rational
open import truncation

import rational.proper-interval as closed
import rational.proper-interval.containment as closed

ℚ∈Iℚ : ℚ -> Pred Iℚ ℓ-zero
ℚ∈Iℚ q a = (Iℚ.l a) < q × q < (Iℚ.u a)

ℚ∈Iℚ-⊆ : {q : ℚ} -> {a b : Iℚ} -> (a i⊆ b) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q b
ℚ∈Iℚ-⊆ (i⊆-cons bl≤al au≤bu) (al<q , q<au) =
  trans-≤-< bl≤al al<q , trans-<-≤ q<au au≤bu

ℚ∈Iℚ-⊂ : {q : ℚ} -> {a b : Iℚ} -> (a i⊂ b) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q b
ℚ∈Iℚ-⊂ (i⊂-cons bl<al au<bu) (al<q , q<au) =
  trans-< bl<al al<q , trans-< q<au au<bu

isProp-ℚ∈Iℚ : (q : ℚ) (a : Iℚ) -> isProp (ℚ∈Iℚ q a)
isProp-ℚ∈Iℚ _ _ = isProp× isProp-< isProp-<


OI->CI-preserves-ℚ∈Iℚ : {q : ℚ} (a : Iℚ) -> ℚ∈Iℚ q a -> closed.ℚ∈Iℚ q (OI->CI a)
OI->CI-preserves-ℚ∈Iℚ _ (al<q , q<au) = weaken-< al<q , weaken-< q<au

tighten-ℚ∈Iℚ : (q : ℚ) (a : Iℚ) -> ℚ∈Iℚ q a -> ∃[ a' ∈ Iℚ ] (ℚ∈Iℚ q a' × a' i⊂ a)
tighten-ℚ∈Iℚ q a@(Iℚ-cons al au al<au) (al<q , q<au) =
  ∥-map2 handle (dense-< al<q) (dense-< q<au)
  where
  handle : Σ[ al' ∈ ℚ ] (al < al' × al' < q) ->
           Σ[ au' ∈ ℚ ] (q < au' × au' < au) ->
           Σ[ a' ∈ Iℚ ] (ℚ∈Iℚ q a' × a' i⊂ a)
  handle (al' , al<al' , al'<q) (au' , q<au' , au'<au) =
    (Iℚ-cons al' au' (trans-< al'<q q<au')),
    (al'<q , q<au'),
    (i⊂-cons al<al' au'<au)

opaque
  ℚ∈Iℚ-* : {q r : ℚ} (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ r b -> ℚ∈Iℚ (q * r) (a i* b)
  ℚ∈Iℚ-* {q} {r} a b q∈a r∈b =
    unsquash (isProp-ℚ∈Iℚ (q * r) (a i* b))
      (∥-map2 ans (tighten-ℚ∈Iℚ q a q∈a) (tighten-ℚ∈Iℚ r b r∈b))
    where
    module _ ((a' , q∈a' , a'⊂a) : Σ[ a' ∈ Iℚ ] (ℚ∈Iℚ q a' × a' i⊂ a))
             ((b' , r∈b' , b'⊂b) : Σ[ b' ∈ Iℚ ] (ℚ∈Iℚ r b' × b' i⊂ b))
      where
      a'b'⊂ab : (a' i* b') i⊂ (a i* b)
      a'b'⊂ab = i*-preserves-⊂ a'⊂a b'⊂b

      rec : closed.ℚ∈Iℚ (q * r) (OI->CI a' closed.i* OI->CI b')
      rec = closed.ℚ∈Iℚ-* (OI->CI a') (OI->CI b')
              (OI->CI-preserves-ℚ∈Iℚ a' q∈a')
              (OI->CI-preserves-ℚ∈Iℚ b' r∈b')

      ans : ℚ∈Iℚ (q * r) (a i* b)
      ans = trans-<-≤ (_i⊂_.l a'b'⊂ab) (proj₁ rec) ,
            trans-≤-< (proj₂ rec) (_i⊂_.u a'b'⊂ab)
