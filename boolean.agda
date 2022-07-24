{-# OPTIONS --cubical --safe --exact-split #-}

module boolean where

open import base
open import equality
open import functions
open import relation


Bool : Boolean -> Type₀
Bool true = Top
Bool false = Bot

true!=false : true != false
true!=false t=f = bot-elim (subst Bool t=f tt)

Discrete-Boolean : Discrete Boolean
Discrete-Boolean true true = yes refl
Discrete-Boolean true false = no true!=false
Discrete-Boolean false true = no (true!=false ∘ sym)
Discrete-Boolean false false = yes refl
