{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module ordered-set.fin where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import functions
open import hlevel
open import isomorphism
open import nat.order.base
open import order
open import order.instances.fin
open import order.instances.fint
open import ordered-set
open import ordered-set.glist

LOSet-Fin : Nat -> LOSet ℓ-zero ℓ-zero
LOSet-Fin n = Fin n , useⁱ

LOSet-FinT : Nat -> LOSet ℓ-zero ℓ-zero
LOSet-FinT n = FinT n , useⁱ

private
  same-< : (n : Nat) (i j : FinT n) -> i < j ≃ (eqFun (FinT≃Fin n) i < eqFun (FinT≃Fin n) j)
  same-< zero ()
  same-< (suc n) (inj-l tt) (inj-l tt) =
    isoToEquiv (isProp->iso (\()) (bot-elim ∘ irrefl-<) isProp-< isProp-<)
  same-< (suc n) (inj-r _) (inj-l tt) =
    isoToEquiv (isProp->iso (\()) (bot-elim ∘ zero-≮ ∘ fin<⁻) isProp-< isProp-<)
  same-< (suc n) (inj-l tt) (inj-r _) =
    isoToEquiv (isProp->iso (\_ -> fin< zero-<) (\_ -> finT<-lr) isProp-< isProp-<)
  same-< (suc n) (inj-r i) (inj-r j) = fint-eq >eq> rec-eq >eq> fin-eq
    where
    rec-eq = same-< n i j

    fint-eq : (inj-r i < inj-r j) ≃ (i < j)
    fint-eq = isoToEquiv (isProp->iso (\{ (finT<-rr lt) -> lt}) (finT<-rr) isProp-< isProp-<)

    fin-eq : (eqFun (FinT≃Fin n) i < eqFun (FinT≃Fin n) j) ≃
             (eqFun (FinT≃Fin (suc n)) (inj-r i) < eqFun (FinT≃Fin (suc n)) (inj-r j))
    fin-eq =
      isoToEquiv (isProp->iso (fin< ∘ suc-≤ ∘ fin<⁻) (fin< ∘ pred-≤ ∘ fin<⁻) isProp-< isProp-<)

module _ (n : Nat) where
  LOSet≃-FinT-Fin : LOSet≃ (LOSet-FinT n) (LOSet-Fin n)
  LOSet≃-FinT-Fin =
    FinT≃Fin n ,
    (record { preserves-< = eqFun (same-< n _ _) } ,
     record { preserves-< = backward-< })
    where
    backward-< : {x y : Fin n} -> x < y -> eqInv (FinT≃Fin n) x < eqInv (FinT≃Fin n) y
    backward-< lt = eqInv e (subst2 _<_ (sym (eqSec (FinT≃Fin n) _))
                                        (sym (eqSec (FinT≃Fin n) _)) lt)
      where
      e = (same-< n _ _)

Indices-FinT=Fin :
  Path (Indices ℓ-zero ℓ-zero ℓ-zero)
    (Nat , (\n -> (LOSet-FinT n) , useⁱ))
    (Nat , (\n -> (LOSet-Fin n) , useⁱ))
Indices-FinT=Fin = \i -> Nat , (\n -> (lo-path n i , dlo-path n i))
  where
  lo-path : (n : Nat) -> (LOSet-FinT n == LOSet-Fin n)
  lo-path n = LOSet≃->path (LOSet≃-FinT-Fin n)

  dlo-path : (n : Nat) -> PathP (\i -> DecidableLinearOrderStr (snd (lo-path n i))) useⁱ useⁱ
  dlo-path n = isProp->PathP (\_ -> isProp-DecidableLinearOrderStr)
