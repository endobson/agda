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

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ


--- Show that Fin 0 and Fin 1 are just Bot and Top
Fin-Bot : Fin 0 == Bot
Fin-Bot = ua (isoToEquiv i)
  where
  i : Iso (Fin 0) Bot
  i .fun (_ , p) = zero-≮ p
  i .inv ()
  i .rightInv ()
  i .leftInv  (_ , p) = bot-elim (zero-≮ p)


Fin-Top : Fin 1 == Top
Fin-Top = ua (isoToEquiv i)
  where
  i : Iso (Fin 1) Top
  i .fun _ = tt
  i .inv _ = zero-fin
  i .rightInv tt = refl
  i .leftInv  (zero  , _)  = ΣProp-path isProp≤ refl
  i .leftInv  (suc i , lt) = bot-elim (zero-≮ (pred-≤ lt))

-- Fin is injective

private
  Fin-suc-⊎ : (n : Nat) -> Fin (suc n) == (Top ⊎ Fin n)
  Fin-suc-⊎ n = ua (isoToEquiv i)
    where

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
  bot-elim (transport (sym path >=> Fin-Bot) zero-fin)
Fin-injective {suc m} {zero}  path =
  bot-elim (transport (path >=> Fin-Bot) zero-fin)
Fin-injective {suc m} {suc n} path = cong suc (Fin-injective path')
  where
  path' : Fin m == Fin n
  path' = ⊎-Top (sym (Fin-suc-⊎ m) >=> path >=> Fin-suc-⊎ n)


private
  Fin-suc-× : (n : Nat) -> (Fin (suc n) × A) == (A ⊎ (Fin n × A))
  Fin-suc-× {A = A} n = ua (isoToEquiv i)
    where
    i : Iso (Fin (suc n) × A) (A ⊎ (Fin n × A))
    i .fun ((0     , p) , a) = (inj-l a)
    i .fun ((suc n , p) , a) = (inj-r ((n , pred-≤ p) , a))
    i .inv (inj-l a)       = (zero-fin  , a)
    i .inv (inj-r (j , a)) = (suc-fin j , a)
    i .rightInv (inj-l _) = refl
    i .rightInv (inj-r (j@(j' , p) , a)) k =
      (inj-r ((j' , isProp≤ (pred-≤ (suc-≤ p)) p k) , a))
    i .leftInv ((0     , p) , a) =
      cong (_, a) (ΣProp-path isProp≤ refl)
    i .leftInv ((suc n , p) , a) =
      cong (_, a) (ΣProp-path isProp≤ refl)

Fin-+ : (m n : Nat) -> Fin (m +' n) == (Fin m ⊎ Fin n)
Fin-+ zero    n = sym (cong (_⊎ Fin n) Fin-Bot >=> ⊎-Bot (Fin n))
Fin-+ (suc m) n =
  Fin-suc-⊎ (m +' n)
  >=> cong (Top ⊎_) (Fin-+ m n)
  >=> sym (⊎-assoc Top (Fin m) (Fin n))
  >=> cong (_⊎ (Fin n)) (sym (Fin-suc-⊎ m))

Fin-* : (m n : Nat) -> Fin (m *' n) == (Fin m × Fin n)
Fin-* zero n = Fin-Bot >=> sym (×-Bot₀ (Fin n)) >=> (cong (_× (Fin n)) (sym Fin-Bot))
Fin-* (suc m) n =
  Fin-+ n (m *' n)
  >=> (cong (Fin n ⊎_) (Fin-* m n))
  >=> sym (Fin-suc-× m)
