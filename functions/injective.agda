{-# OPTIONS --cubical --safe --exact-split #-}

module functions.injective where

open import base
open import boolean
open import cubical
open import equality-path
open import functions
open import truncation

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Type ℓ

Injective-2of3₃ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                  isComposition f g h ->
                  Injective f -> Injective g -> Injective h
Injective-2of3₃ c inj-f inj-g p = inj-g (inj-f (c _ >=> p >=> sym (c _)))


Injective-2of3₂ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                  isComposition f g h ->
                  Injective f -> Injective h -> Injective g
Injective-2of3₂ {f = f} c inj-f inj-h p = inj-h (sym (c _) >=> cong f p >=> c _)


¬Injective-2of3₁ : ¬ ({A : Type₀} {B : Type₀} {C : Type₀}
                      {f : B -> C} {g : A -> B} {h : A -> C} ->
                      isComposition f g h ->
                      Injective g -> Injective h -> Injective f)
¬Injective-2of3₁ inj-f = ¬inj-f (inj-f c inj-g inj-h)
  where
  f : Boolean -> Top
  f true = tt
  f false = tt
  g : Top -> Boolean
  g tt = true
  h : Top -> Top
  h x = x
  c : isComposition f g h
  c tt = refl
  inj-g : Injective g
  inj-g {tt} {tt} p = refl
  inj-h : Injective h
  inj-h {tt} {tt} p = refl


  ¬inj-f : ¬ (Injective f)
  ¬inj-f inj-f = true!=false (inj-f refl)

Retraction->Injective : {f : A -> B} -> Retraction f -> Injective f
Retraction->Injective {f = f} (g , ret-g) p = sym (ret-g _) >=> cong g p >=> (ret-g _)

Section->Surjection : {f : A -> B} -> Section f -> isSurjection f
Section->Surjection {f = f} (g , sec-g) b = ∣ g b , sec-g b ∣
