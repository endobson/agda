{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.boolean where

open import base
open import boolean
open import equality-path
open import equivalence
open import funext
open import hlevel.base
open import isomorphism
open import order
open import relation
open import truncation
open import univalence

data Boolean< : Rel Boolean ℓ-zero where
  false<true : Boolean< false true

private
  Boolean<->¬Bool₁ : ∀ {x} {y} -> Boolean< x y -> ¬ (Bool x)
  Boolean<->¬Bool₁ false<true b = b
  Boolean<->Bool₂ : ∀ {x} {y} -> Boolean< x y -> Bool y
  Boolean<->Bool₂ false<true = tt

  isProp-Boolean< : ∀ x y -> isProp (Boolean< x y)
  isProp-Boolean< x y = isProp-Boolean<' x y x y refl refl
    where
    isProp-Boolean<' : ∀ a b c d -> (p1 : a == c) -> (p2 : b == d) ->
      (l1 : Boolean< a b) (l2 : Boolean< c d) -> PathP (\i -> Boolean< (p1 i) (p2 i)) l1 l2
    isProp-Boolean<' _ _ _ _ p1 p2 l1@false<true l2@false<true =
      transport (\i -> PathP (\j -> Boolean< (isSet-Boolean false false refl p1 i j)
                                             (isSet-Boolean true true refl p2 i j)) l1 l2)
        refl

  trans-Boolean< : ∀ x y z -> Boolean< x y -> Boolean< y z -> Boolean< x z
  trans-Boolean< _ _ _ false<true ()

  irrefl-Boolean< : ∀ x -> ¬ (Boolean< x x)
  irrefl-Boolean< true x<x = Boolean<->¬Bool₁ x<x tt
  irrefl-Boolean< false x<x = Boolean<->Bool₂ x<x

  comparison-Boolean< : ∀ x y z -> Boolean< x z -> ∥ Boolean< x y ⊎ Boolean< y z ∥
  comparison-Boolean< _ false _ false<true = ∣ inj-r false<true ∣
  comparison-Boolean< _ true _ false<true = ∣ inj-l false<true ∣

  connected-Boolean< : ∀ x y -> ¬ (Boolean< x y) -> ¬ (Boolean< y x) -> x == y
  connected-Boolean< false false x≮y y≮x = refl
  connected-Boolean< false true  x≮y y≮x = bot-elim (x≮y false<true)
  connected-Boolean< true  false x≮y y≮x = bot-elim (y≮x false<true)
  connected-Boolean< true  true  x≮y y≮x = refl

instance
  opaque
    isLinearOrder-Boolean< : isLinearOrder Boolean<
    isLinearOrder-Boolean< = record
      { isProp-< = isProp-Boolean< _ _
      ; irrefl-< = irrefl-Boolean< _
      ; trans-< = trans-Boolean< _ _ _
      ; comparison-< = comparison-Boolean<
      ; connected-< = connected-Boolean< _ _
      }

data Boolean≤ : Rel Boolean ℓ-zero where
  false≤false : Boolean≤ false false
  false≤true : Boolean≤ false true
  true≤true : Boolean≤ true true

private
  Boolean≮->Boolean≤ : ∀ x y -> ¬(Boolean< y x) -> Boolean≤ x y
  Boolean≮->Boolean≤ false false _ = false≤false
  Boolean≮->Boolean≤ false true  _ = false≤true
  Boolean≮->Boolean≤ true  true  _ = true≤true
  Boolean≮->Boolean≤ true  false ¬f<t = bot-elim (¬f<t false<true)

  Boolean≤->Boolean≮ : ∀ x y -> Boolean≤ y x -> ¬ (Boolean< x y)
  Boolean≤->Boolean≮ _ _ le lt = Boolean≤->Boolean≮' lt le
    where
    Boolean≤->Boolean≮' : ∀ {x} {y} -> Boolean< x y -> Boolean≤ y x -> Bot
    Boolean≤->Boolean≮' false<true ()

  Boolean≤-Boolean≮-eq : ∀ x y -> (Boolean≤ x y) ≃ (¬ (Boolean< y x))
  Boolean≤-Boolean≮-eq x y =
    isoToEquiv (iso (Boolean≤->Boolean≮ y x) (Boolean≮->Boolean≤ x y) (\_ -> isProp¬ _ _ _) bf)
    where
    bf : ∀ {x} {y} z -> Boolean≮->Boolean≤ x y (Boolean≤->Boolean≮ y x z) == z
    bf false≤false = refl
    bf false≤true = refl
    bf true≤true = refl

instance
  opaque
    isPartialOrder-Boolean≤ : isPartialOrder Boolean≤
    isPartialOrder-Boolean≤ =
      transport (cong isPartialOrder p) (isLinearOrder->isPartialOrder-≯ useⁱ)
      where
      p : (\x y -> ¬ (Boolean< y x)) == Boolean≤
      p = funExt2 (\x y -> sym (ua (Boolean≤-Boolean≮-eq x y)))

    CompatibleOrderStr-Boolean≤ : CompatibleOrderStr isLinearOrder-Boolean< isPartialOrder-Boolean≤
    CompatibleOrderStr-Boolean≤ = record
      { convert-≮ = Boolean≮->Boolean≤ _ _
      }
