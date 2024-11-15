{-# OPTIONS --cubical --safe --exact-split #-}

module fin-algebra where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import funext
open import isomorphism
open import maybe
open import nat
open import nat.order
open import order
open import order.instances.nat
open import sum
open import type-algebra
open import univalence
open import vec

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ


--- Show that Fin 0 and Fin 1 are just Bot and Top
Fin-Bot-iso : Iso (Fin 0) Bot
Fin-Bot-iso = i
  where
  i : Iso (Fin 0) Bot
  i .fun (_ , p) = zero-≮ p
  i .inv ()
  i .rightInv ()
  i .leftInv  (_ , p) = bot-elim (zero-≮ p)

Fin-Bot-eq : Fin 0 ≃ Bot
Fin-Bot-eq = isoToEquiv Fin-Bot-iso

Fin-Bot : Fin 0 == Bot
Fin-Bot = ua Fin-Bot-eq


Fin-Top-eq : Fin 1 ≃ Top
Fin-Top-eq = (isoToEquiv i)
  where
  i : Iso (Fin 1) Top
  i .fun _ = tt
  i .inv _ = zero-fin
  i .rightInv tt = refl
  i .leftInv  (zero  , _)  = fin-i-path refl
  i .leftInv  (suc i , lt) = bot-elim (zero-≮ (pred-≤ lt))

Fin-Top : Fin 1 == Top
Fin-Top = ua Fin-Top-eq

-- Fin is injective

Fin-suc-⊎-eq : (n : Nat) -> Fin (suc n) ≃ (Top ⊎ Fin n)
Fin-suc-⊎-eq n = isoToEquiv i
  where
  i : Iso (Fin (suc n)) (Top ⊎ Fin n)
  i .fun (zero  , p) = inj-l tt
  i .fun (suc i , p) = inj-r (i , pred-≤ p)
  i .inv (inj-l _)   = zero-fin
  i .inv (inj-r j)   = suc-fin j
  i .rightInv (inj-l _)  = refl
  i .rightInv (inj-r j)  = cong inj-r (fin-i-path refl)
  i .leftInv (zero  , p) = (fin-i-path refl)
  i .leftInv (suc i , p) = (fin-i-path refl)

Fin-suc-⊎ : (n : Nat) -> Fin (suc n) == (Top ⊎ Fin n)
Fin-suc-⊎ n = ua (Fin-suc-⊎-eq n)

Fin-Maybe-eq : (n : Nat) -> Fin (suc n) ≃ Maybe (Fin n)
Fin-Maybe-eq n = isoToEquiv i
  where
  i : Iso (Fin (suc n)) (Maybe (Fin n))
  i .fun (zero  , p) = nothing
  i .fun (suc i , p) = just (i , pred-≤ p)
  i .inv nothing     = zero-fin
  i .inv (just j)    = suc-fin j
  i .rightInv nothing    = refl
  i .rightInv (just j)   = cong just (fin-i-path refl)
  i .leftInv (zero  , p) = (fin-i-path refl)
  i .leftInv (suc i , p) = (fin-i-path refl)


isInjective-Fin : isInjective Fin
isInjective-Fin {zero}  {zero}  path = refl
isInjective-Fin {zero}  {suc n} path =
  bot-elim (transport (sym path >=> Fin-Bot) zero-fin)
isInjective-Fin {suc m} {zero}  path =
  bot-elim (transport (path >=> Fin-Bot) zero-fin)
isInjective-Fin {suc m} {suc n} path = cong suc (isInjective-Fin path')
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
      (inj-r ((j' , isProp-≤ (pred-≤ (suc-≤ p)) p k) , a))
    i .leftInv ((0     , p) , a) = \i -> p2 i , a
      where
      p2 : Path (Fin (suc n)) zero-fin (0 , p)
      p2 = fin-i-path refl
    i .leftInv ((suc n2 , p) , a) = \i -> p2 i , a
      where
      p2 : Path (Fin (suc n)) (suc n2 , (suc-≤ (pred-≤ p))) (suc n2 , p)
      p2 = fin-i-path refl

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


Fin-Fun : {n : Nat} (A : Type₀) -> (Fin n -> A) == Vec A n
Fin-Fun {zero} A =
  (\i -> Fin-Bot i -> A)
  >=> Bot-Fun A
  >=> sym (Vec-Top A)
Fin-Fun {suc n} A =
  (\i -> Fin-suc-⊎ n i -> A)
  >=> (⊎-Fun Top (Fin n) A)
  >=> (\i -> Top-Fun A i × Fin-Fun {n} A i)
  >=> sym (Vec-× A)

FinT : Nat -> Type₀
FinT zero = Bot
FinT (suc n) = Top ⊎ FinT n

FinT=Fin : (n : Nat) -> FinT n == Fin n
FinT=Fin zero = sym Fin-Bot
FinT=Fin (suc n) = cong (Top ⊎_) (FinT=Fin n) >=> sym (Fin-suc-⊎ n)

FinT≃Fin : (n : Nat) -> FinT n ≃ Fin n
FinT≃Fin zero = equiv⁻¹ Fin-Bot-eq
FinT≃Fin (suc n) = ⊎-equiv (idEquiv Top) (FinT≃Fin n) >eq> equiv⁻¹ (Fin-suc-⊎-eq n)

isInjective-FinT : isInjective FinT
isInjective-FinT = subst isInjective (sym (funExt FinT=Fin)) isInjective-Fin
