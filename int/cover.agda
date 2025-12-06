{-# OPTIONS --cubical --safe --exact-split #-}

module int.cover where

open import base
open import decision
open import discrete
open import equality-path
open import hlevel.base
open import int.base
open import nat

private
  IntEqCover : ℤ -> ℤ -> Type₀
  IntEqCover (nonneg x) (nonneg y) = x == y
  IntEqCover (nonneg x) (neg y) = Bot
  IntEqCover (neg x) (nonneg y) = Bot
  IntEqCover (neg x) (neg y) = x == y

  cover->path : {a b : ℤ} -> IntEqCover a b -> a == b
  cover->path {nonneg x} {nonneg y} p = cong nonneg p
  cover->path {nonneg x} {neg y}    b = bot-elim b
  cover->path {neg x}    {nonneg y} b = bot-elim b
  cover->path {neg x}    {neg y}    p = cong neg p

  refl-cover : ∀ a -> IntEqCover a a
  refl-cover (nonneg x) = refl
  refl-cover (neg x) = refl

  path->cover : ∀ {a b : ℤ} -> a == b -> IntEqCover a b
  path->cover {a} = J (\b _ -> IntEqCover a b) (refl-cover a)

opaque
  nonneg-injective : {m n : Nat} -> nonneg m == nonneg n -> m == n
  nonneg-injective = path->cover
  neg-injective : {m n : Nat} -> neg m == neg n -> m == n
  neg-injective = path->cover

private
  decide-int-cover : (a b : ℤ) -> Dec (IntEqCover a b)
  decide-int-cover (nonneg x) (nonneg y) = decide-nat x y
  decide-int-cover (nonneg x) (neg y)    = no (\x -> x)
  decide-int-cover (neg x)    (nonneg y) = no (\x -> x)
  decide-int-cover (neg x)    (neg y)    = decide-nat x y

opaque
  decide-int : (a b : ℤ) -> Dec (a == b)
  decide-int a b = case (decide-int-cover a b) of
    (\{ (yes c) -> yes (cover->path c)
      ; (no ¬c) -> no (\p -> ¬c (path->cover p))
      })

  discreteInt : Discrete Int
  discreteInt = decide-int

  isSetInt : isSet Int
  isSetInt = Discrete->isSet discreteInt
