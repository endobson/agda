{-# OPTIONS --cubical --safe --exact-split #-}

module functions.sections where

open import base
open import cubical
open import equality-path
open import functions

private
  variable
    ℓ : Level
    A B C : Type ℓ

Section-2of3₃ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                isComposition f g h -> 
                Section f -> Section g -> Section h
Section-2of3₃ {f = f} {g = g} c (f' , sec-f) (g' , sec-g) = 
  g' ∘ f' , \ x -> sym (c _) >=> cong f (sec-g (f' x)) >=> sec-f x

Retraction-2of3₃ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                   isComposition f g h -> 
                   Retraction f -> Retraction g -> Retraction h
Retraction-2of3₃ {f = f} {g = g} c (f' , ret-f) (g' , ret-g) = 
  g' ∘ f' , \ x -> cong (g' ∘ f') (sym (c x)) >=> cong g' (ret-f (g x)) >=> ret-g x


-- Section-2of3₂ : {f : B -> C} {g : A -> B} {h : A -> C} ->
--                 isComposition f g h -> 
--                 Section f -> Section h -> Section g
-- Section-2of3₂ {f = f} {g = g} {h = h} c (f' , sec-f) (h' , sec-h) = 
--   h' ∘ f , \x -> ?
--   where
--   sec-f' : ∀ x -> f (f' x) == x
--   sec-f' = sec-f
