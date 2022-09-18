{-# OPTIONS --cubical --safe --exact-split #-}

module transport where

open import base
open import equality-path
open import equivalence
open import cubical
open import functions
open import univalence
open import funext


module _ {ℓ : Level} {A B : Type ℓ} (eq : A ≃ B) where
  transportβ-ua : (a : A) -> transport (ua eq) a == eqFun eq a
  transportβ-ua a = transportRefl (eqFun eq a)


module _ {ℓ ℓC : Level} {A B : Type ℓ} {C : Type ℓC} (p : A == B) where
  transportβ-fun-codomain : (f : C -> A) -> 
    transport (\i -> C -> p i) f == (\c -> transport p (f c))
  transportβ-fun-codomain f i c = 
    (transp (\j -> p j) i0 (f (transp (\j -> C) i c)))

  transportβ-fun-domain : (f : A -> C) -> 
    transport (\i -> p i -> C) f == (\b -> (f (transport (sym p) b)))
  transportβ-fun-domain f i b =
    (transp (\j -> C) i (f (transp (\j -> p (~ j)) i0 b)))


private
  module _ {ℓ : Level} {A B C : Type ℓ} (eq : A ≃ B) where

    example1 : (f : C -> A) -> transport (\i -> C -> ua eq i) f == eqFun eq ∘ f
    example1 f =
      transportβ-fun-codomain (ua eq) f >=> 
      funExt (\c -> transportβ-ua eq (f c))
