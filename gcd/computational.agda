{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.computational where

open import base
open import div
open import gcd.propositional using (GCD' ; GCD⁺)
open import gcd.euclidean-algorithm
open import nat
open import int

module gprop = gcd.propositional

gcd' : Nat -> Nat -> Nat
gcd' a b = fst (gcd'-exists a b)

gcd'-proof : (a b : Nat) -> GCD' a b (gcd' a b)
gcd'-proof a b = snd (gcd'-exists a b)

gcd⁺ : Nat⁺ -> Nat⁺ -> Nat⁺
gcd⁺ (a , a-pos) (b , _) = gcd' a b , div'-pos->pos (GCD'.%a (gcd'-proof a b)) a-pos

gcd⁺-proof : (a b : Nat⁺) -> GCD⁺ a b (gcd⁺ a b)
gcd⁺-proof (a , _) (b , _) = gcd'-proof a b

gcd'-unique : {a b n : Nat} -> GCD' a b n -> gcd' a b == n
gcd'-unique g = gprop.gcd'-unique (gcd'-proof _ _) g
