{-# OPTIONS --cubical --safe --exact-split #-}

module new-permutation where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import isomorphism
open import hlevel
open import nat
open import relation
open import sigma

open Iso

Perm : Nat -> Type₀
Perm n = Auto (Fin n)

-- Identity permutation
idPerm : {n : Nat} -> Perm n
idPerm = id-iso

-- Permutation that holds 'zero-fin' constant and acts like the shifted argument otherwise
suc-fin-f : {n : Nat} -> (Fin n -> Fin n) -> (Fin (suc n) -> Fin (suc n))
suc-fin-f f (zero  , lt) = (zero , lt)
suc-fin-f f (suc i , lt) = (suc-fin ∘ f) (i , pred-≤ lt)

private
  suc-fin-f-compose-path : {n : Nat} (f : Fin n -> Fin n) ->
    (suc-fin-f f ∘ suc-fin) == (suc-fin ∘ f)
  suc-fin-f-compose-path f k (i , p) = path k
    where
    lemma : (suc (f (i , pred-≤ (suc-≤ p)) .fst)) == suc (f (i , p) .fst)
    lemma k = (suc (f (i , isProp≤ (pred-≤ (suc-≤ p)) p k) .fst))

    path : (suc-fin-f f ∘ suc-fin) (i , p) == (suc-fin ∘ f) (i , p)
    path = ΣProp-path isProp≤ lemma

  suc-fin-f-double-compose-path : {n : Nat} (f : Fin n -> Fin n) (g : Fin n -> Fin n) ->
    (suc-fin-f f ∘ suc-fin-f g ∘ suc-fin) == (suc-fin ∘ f ∘ g)
  suc-fin-f-double-compose-path f g =
    cong (suc-fin-f f ∘_) (suc-fin-f-compose-path g)
    >=> cong (_∘ g) (suc-fin-f-compose-path f)

  fin-fun-eq-split-zero : {ℓ : Level} {A : Type ℓ} {n : Nat} {f g : Fin (suc n) -> A}
                          -> (f zero-fin) == (g zero-fin)
                          -> (f ∘ suc-fin) == (g ∘ suc-fin)
                          -> f == g
  fin-fun-eq-split-zero {f = f} {g = g} zp sp i (zero , p) =
    ((cong f path) ∙∙ zp ∙∙ (cong g (sym path))) i
    where
    path : (zero , p) == zero-fin
    path = ΣProp-path isProp≤ refl
  fin-fun-eq-split-zero {f = f} {g = g} zp sp i (suc j , p) =
    ((cong f path) ∙∙ (\i -> sp i (j , (pred-≤ p))) ∙∙ (cong g (sym path))) i

    where
    path : (suc j , p) == suc-fin (j , (pred-≤ p))
    path = ΣProp-path isProp≤ refl

  sucPerm-rightInv : {n : Nat} (φ : Perm n)
                     -> suc-fin-f (φ .fun) ∘ suc-fin-f (φ .inv) == idfun (Fin (suc n))
  sucPerm-rightInv φ = fin-fun-eq-split-zero refl lemma
    where
    lemma : suc-fin-f (φ .fun) ∘ suc-fin-f (φ .inv) ∘ suc-fin == suc-fin
    lemma = (suc-fin-f-double-compose-path (φ .fun) (φ .inv))
            >=> (cong (suc-fin ∘_) (\i a -> φ .rightInv a i))
  sucPerm-leftInv : {n : Nat} (φ : Perm n)
                     -> suc-fin-f (φ .inv) ∘ suc-fin-f (φ .fun) == idfun (Fin (suc n))
  sucPerm-leftInv φ = fin-fun-eq-split-zero refl lemma
    where
    lemma : suc-fin-f (φ .inv) ∘ suc-fin-f (φ .fun) ∘ suc-fin == suc-fin
    lemma = (suc-fin-f-double-compose-path (φ .inv) (φ .fun))
            >=> (cong (suc-fin ∘_) (\i a -> φ .leftInv a i))

sucPerm : {n : Nat} -> Perm n -> Perm (suc n)
sucPerm φ .fun = suc-fin-f (φ .fun)
sucPerm φ .inv = suc-fin-f (φ .inv)
sucPerm φ .rightInv s i = sucPerm-rightInv φ i s
sucPerm φ .leftInv  s i = sucPerm-leftInv φ i s
