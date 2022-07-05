{-# OPTIONS --cubical --safe --exact-split #-}

module maybe where

open import base
open import equality

private
  variable
    ℓ : Level
    A B : Type ℓ

data Maybe (A : Type ℓ) : Type ℓ where
 nothing : Maybe A
 just : A -> Maybe A

Just : Maybe A -> Type₀
Just nothing = Bot
Just (just _) = Top

Nothing : Maybe A -> Type₀
Nothing nothing = Top
Nothing (just _) = Bot

just-v : (m : Maybe A) -> Just m -> A
just-v (just v) _ = v

maybe : (b : B) (f : A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

just-injective : {a1 a2 : A} -> (just a1) == (just a2) -> a1 == a2
just-injective {a1 = a1} p = cong (maybe a1 (\x -> x)) p

just!=nothing : {a : A} -> just a != nothing
just!=nothing p = transport (\i -> Just (p i)) tt
