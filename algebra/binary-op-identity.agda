{-# OPTIONS --cubical --safe --exact-split #-}

module algebra.binary-op-identity where

open import base
open import equality-path
open import hlevel.base
open import hlevel.htype

hasIdentityElem : {ℓ : Level} -> Σ[ (D , _) ∈ hSet ℓ ] (D -> D -> D) -> Type ℓ
hasIdentityElem ((D , _) , op) =
  Σ[ ε ∈ D ] ((∀ x -> op ε x == x) × ∀ x -> op x ε == x)

opaque
  isProp-hasIdentityElem : {ℓ : Level} -> (op : Σ[ (D , _) ∈ hSet ℓ ] (D -> D -> D)) ->
                           isProp (hasIdentityElem op)
  isProp-hasIdentityElem ((D , isSet-D) , op) (ε₁ , l₁ , r₁) (ε₂ , l₂ , r₂) =
    \i -> εp i , lp i , rp i
    where
    εp : ε₁ == ε₂
    εp = sym (l₂ ε₁) >=> r₁ ε₂

    lp : PathP (\i -> ∀ x -> op (εp i) x == x) l₁ l₂
    lp = isProp->PathP (\_ -> isPropΠ (\x -> isSet-D _ _))
    rp : PathP (\i -> ∀ x -> op x (εp i) == x) r₁ r₂
    rp = isProp->PathP (\_ -> isPropΠ (\x -> isSet-D _ _))
