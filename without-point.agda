{-# OPTIONS --cubical --safe --exact-split #-}

module without-point where

open import base
open import equality
open import relation
open import sigma
open import sigma.base
open import hlevel
open import functions

WithoutPoint : {ℓ : Level} (A : Type ℓ) -> (a : A) -> Type ℓ
WithoutPoint A a = Σ[ a2 ∈ A ] (a2 != a)

Discrete-WithoutPoint : 
  {ℓ : Level} {A : Type ℓ} -> (Discrete A) -> (a : A) -> Discrete (WithoutPoint A a)
Discrete-WithoutPoint discA _ (a2 , _) (a3 , _) with discA a2 a3
... | (yes a2=a3) = yes (ΣProp-path (isProp¬ _) a2=a3)
... | (no a2!=a3) = no (a2!=a3 ∘ cong fst)
