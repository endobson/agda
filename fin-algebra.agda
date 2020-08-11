{-# OPTIONS --cubical --safe --exact-split #-}

module fin-algebra where

open import base
open import equality
open import equivalence
open import fin
open import type-algebra
open import isomorphism
open import nat
open import functions
open import sigma

--- Show that Fin 0 and Fin 1 are just Bot and Top
private
  fin-zero-bot-iso : Iso (Fin 0) Bot
  Iso.fun fin-zero-bot-iso (_ , p) = zero-≮ p
  Iso.inv fin-zero-bot-iso ()
  Iso.rightInv fin-zero-bot-iso ()
  Iso.leftInv  fin-zero-bot-iso (_ , p) = bot-elim (zero-≮ p)

  fin-one-top-iso : Iso (Fin 1) Top
  Iso.fun fin-one-top-iso _ = tt
  Iso.inv fin-one-top-iso _ = zero-fin
  Iso.rightInv fin-one-top-iso tt           = refl
  Iso.leftInv  fin-one-top-iso (zero  , _)  = ΣProp-path isProp≤ refl
  Iso.leftInv  fin-one-top-iso (suc i , lt) = bot-elim (zero-≮ (pred-≤ lt))

fin-zero-bot-path : Fin 0 == Bot
fin-zero-bot-path = ua (isoToEquiv fin-zero-bot-iso)

fin-one-top-path : Fin 1 == Top
fin-one-top-path = ua (isoToEquiv fin-one-top-iso)


-- Fin is injective

private
  Fin-suc-⊎ : (n : Nat) -> Fin (suc n) == (Top ⊎ Fin n)
  Fin-suc-⊎ n = ua (isoToEquiv i)
    where
    open Iso

    i : Iso (Fin (suc n)) (Top ⊎ Fin n)
    i .fun (zero  , p) = inj-l tt
    i .fun (suc i , p) = inj-r (i , pred-≤ p)
    i .inv (inj-l _)   = zero-fin
    i .inv (inj-r j)   = suc-fin j
    i .rightInv (inj-l _)  = refl
    i .rightInv (inj-r j)  = cong inj-r (ΣProp-path isProp≤ refl)
    i .leftInv (zero  , p) = (ΣProp-path isProp≤ refl)
    i .leftInv (suc i , p) = (ΣProp-path isProp≤ refl)

Fin-injective : Injective Fin
Fin-injective {zero}  {zero}  path = refl
Fin-injective {zero}  {suc n} path =
  bot-elim (transport (sym path >=> fin-zero-bot-path) zero-fin)
Fin-injective {suc m} {zero}  path =
  bot-elim (transport (path >=> fin-zero-bot-path) zero-fin)
Fin-injective {suc m} {suc n} path = cong suc (Fin-injective path')
  where
  path' : Fin m == Fin n
  path' = ⊎-Top (sym (Fin-suc-⊎ m) >=> path >=> Fin-suc-⊎ n)
