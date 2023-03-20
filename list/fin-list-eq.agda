{-# OPTIONS --cubical --safe --exact-split #-}

module list.fin-list-eq where

open import base
open import equivalence
open import equality
open import isomorphism
open import list.base
open import sum
open import sigma
open import fin-algebra
open import functions
open import funext
open import type-algebra

import fin.list as fin
import fint.list as fint

List≃FinTList : {ℓ : Level} {A : Type ℓ} -> List A ≃ fint.FinList A
List≃FinTList {A = A} = isoToEquiv (iso forward backward fb bf)
  where
  forward : List A -> fint.FinList A
  forward [] = 0 , \()
  forward (e :: l) = suc (fst rec) , either (\_ -> e) (\i -> (snd rec) i)
    where
    rec = forward l
  backward' : (n : Nat) -> (FinT n -> A) -> List A
  backward' 0 _ = []
  backward' (suc n) f = f (inj-l tt) :: backward' n (f ∘ inj-r)
  backward : fint.FinList A -> List A
  backward (n , f) = backward' n f

  fb' : (n : Nat) -> (f : FinT n -> A) -> forward (backward' n f) == (n , f)
  fb' 0 f = \i -> p1 i , p2 i
    where
    p1 : fst (forward (backward' 0 f)) == 0
    p1 = refl
    p2 : snd (forward (backward' 0 f)) == f
    p2 = funExt (\())
  fb' (suc n) f = \i -> p1 i , p2 i
    where
    rec : forward (backward' n (f ∘ inj-r)) == (n , f ∘ inj-r)
    rec = fb' n (f ∘ inj-r)
    p1 : fst (forward (backward' (suc n) f)) == (suc n)
    p1 i = suc (fst (rec i))
    p2 : PathP (\i -> FinT (p1 i) -> A) (snd (forward (backward' (suc n) f))) f
    p2 = transP-left (\i -> either (\_ -> f (inj-l tt)) (snd (rec i)))
                     (funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl }))


  fb : (as : fint.FinList A) -> forward (backward as) == as
  fb (n , f) = fb' n f

  bf : (as : List A) -> backward (forward as) == as
  bf [] = refl
  bf (e :: l) = cong (e ::_) (bf l)


List≃FinList : {ℓ : Level} {A : Type ℓ} -> List A ≃ fin.FinList A
List≃FinList {A = A} =
 List≃FinTList >eq> (existential-eq (\n -> reindexΠ (equiv⁻¹ (FinT≃Fin n)) (\_ -> A)))
