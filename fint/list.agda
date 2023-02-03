{-# OPTIONS --cubical --safe --exact-split #-}

module fint.list where

open import base
open import equality
open import equivalence.base
open import fin-algebra
open import functions
open import funext
open import hlevel.base
open import isomorphism
open import order.homomorphism
open import order.instances.fint
open import relation
open import sum
open import truncation

private
  variable
    ℓ ℓ< : Level
    A : Type ℓ

FinList : Type ℓ -> Type ℓ
FinList A = Σ[ n ∈ Nat ] (FinT n -> A)

SubSequence : Rel (FinList A) _
SubSequence (n1 , f1) (n2 , f2) =
  ∃[ g ∈ (FinT n1 -> FinT n2) ] (LinearOrderʰ g × ∀ i -> (f1 i) == (f2 (g i)))

_l∈'_ : REL A (FinList A) (levelOf A)
a l∈' (n , f) = Σ[ i ∈ FinT n ] (f i == a)

_l∈_ : REL A (FinList A) (levelOf A)
a l∈ (n , f) = ∃[ i ∈ FinT n ] (f i == a)

finlist-empty : FinList A
finlist-empty = 0 , \()

finlist-cons : A -> FinList A -> FinList A
finlist-cons a (n , f) = (suc n) , either (\_ -> a) f

abstract
  FinList-Ind : {ℓP : Level} (P : Pred (FinList A) ℓP) ->
                (pE : P finlist-empty) ->
                (pC : ∀ (a : A) -> (l : FinList A) ->
                        (P l) -> P (finlist-cons a l)) ->
                (l : FinList A) -> P l
  FinList-Ind {A = A} P pE pC (n , f) = rec n f
    where
    module _ where
      rec : (n : Nat) -> (f : FinT n -> A) -> P (n , f)
      rec 0 f = subst P path pE
        where
        path' : snd (finlist-empty) == f
        path' = funExt (\())

        path : finlist-empty == (0 , f)
        path i = 0 , path' i
      rec (suc n) f = subst P path (pC a l' Pl')
        where

        a : A
        a = f (inj-l tt)
        f' : FinT n -> A
        f' = f ∘ inj-r
        l' : FinList A
        l' = n , f'
        Pl' : P l'
        Pl' = rec n f'

        path' : snd (finlist-cons a l') == f
        path' = funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl })

        path : (finlist-cons a l') == (suc n , f)
        path i = suc n , path' i

finlist-empty-l∈-eq : ∀ (a2 : A) -> (a2 l∈ finlist-empty) ≃ Bot
finlist-empty-l∈-eq a2 = isoToEquiv (isProp->iso (unsquash isPropBot ∘ ∥-map forward)
                                                 backward squash isPropBot)
  where
  forward : a2 l∈' finlist-empty -> Bot
  forward (() , _)
  backward : Bot -> a2 l∈ finlist-empty
  backward ()

finlist-cons-l∈-eq : (a : A) (l : FinList A) ->
                     (∀ a2 -> (a2 l∈ (finlist-cons a l)) ≃ (∥ a2 l∈ l ⊎ a2 == a ∥))
finlist-cons-l∈-eq a l a2 = isoToEquiv (isProp->iso (∥-map forward) (∥-bind backward) squash squash)
  where
  forward : a2 l∈' (finlist-cons a l) -> a2 l∈ l ⊎ a2 == a
  forward (inj-l _ , p) = inj-r (sym p)
  forward (inj-r i , p) = inj-l (∣ i , p ∣)
  backward : (a2 l∈ l ⊎ a2 == a) -> a2 l∈ (finlist-cons a l)
  backward (inj-l a2∈l) = ∥-map (\(i , p) -> (inj-r i) , p) a2∈l
  backward (inj-r a2=a) = ∣ inj-l tt , sym a2=a ∣
