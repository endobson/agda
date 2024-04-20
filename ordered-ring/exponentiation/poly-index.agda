{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation.poly-index where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import fin
open import finset
open import functions
open import hlevel
open import isomorphism
open import nat
open import relation
open import semiring
open import truncation


PolyIndex : (n : ℕ) -> Type₀
PolyIndex n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] (i + j == n)

PolyIndex<->Fin : {n : Nat} -> Iso (PolyIndex n) (Fin (suc n))
PolyIndex<->Fin .Iso.fun (i , j , i+j==n) = i , (j , +-commuteᵉ j (suc i) >=> cong suc i+j==n)
PolyIndex<->Fin .Iso.inv (i , j , p) = i , j , cong pred (+-commuteᵉ (suc i) j >=> p)
PolyIndex<->Fin .Iso.leftInv (i , j , p) = cong (\p -> i , j , p) (isSetNat _ _ _ _)
PolyIndex<->Fin .Iso.rightInv (i , j , p) = cong (\p -> i , j , p) (isSetNat _ _ _ _)

FinSet-PolyIndex : (n : Nat) -> FinSet ℓ-zero
FinSet-PolyIndex n = PolyIndex n , ∣ suc n , isoToEquiv PolyIndex<->Fin ∣

isSet-PolyIndex : {n : Nat} -> isSet (PolyIndex n)
isSet-PolyIndex = isFinSet->isSet (snd (FinSet-PolyIndex _))

instance
  FinSetStr-PolyIndex : {n : Nat} -> FinSetStr (PolyIndex n)
  FinSetStr-PolyIndex {n} .FinSetStr.isFin = ∣ suc n , isoToEquiv PolyIndex<->Fin ∣

PolyIndex-i≠0 : {n : Nat} -> Pred (PolyIndex n) ℓ-zero
PolyIndex-i≠0 (i , j , p) = i != 0
PolyIndex-j≠0 : {n : Nat} -> Pred (PolyIndex n) ℓ-zero
PolyIndex-j≠0 (i , j , p) = j != 0

PolyIndex-i≠0-iso : (n : Nat) -> Iso (PolyIndex n) (Σ (PolyIndex (suc n)) PolyIndex-i≠0)
PolyIndex-i≠0-iso n .Iso.fun (i , j , p) = (suc i , j , cong suc p) , zero-suc-absurd ∘ sym
PolyIndex-i≠0-iso n .Iso.inv ((suc i , j , p) , _) = (i , j , cong pred p)
PolyIndex-i≠0-iso n .Iso.inv ((zero , j , _) , ¬p) = bot-elim (¬p refl)
PolyIndex-i≠0-iso n .Iso.leftInv _ = refl
PolyIndex-i≠0-iso n .Iso.rightInv ((suc i , j , p) , _) =
  cong2 (\p1 p2 -> ((suc i , j , p1) , p2)) (isSetNat _ _ _ _) (isProp¬ _ _ _)
PolyIndex-i≠0-iso n .Iso.rightInv ((zero , j , _) , ¬p) = bot-elim (¬p refl)


module _ {ℓD : Level} {D : Type ℓD}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
  where
  all-ones-pif : (n : Nat) -> (PolyIndex n -> D)
  all-ones-pif _ _ = 1#

module _ {ℓD : Level} {D : Type ℓD}
         {{ACM : AdditiveCommMonoid D}}
  where
  shift₁ : {n : Nat} -> (PolyIndex n -> D) -> PolyIndex (suc n) -> D
  shift₁ f (zero  , j , p) = 0#
  shift₁ f (suc i , j , p) = f (i , j , cong pred p)

  shift₂ : {n : Nat} -> (PolyIndex n -> D) -> PolyIndex (suc n) -> D
  shift₂ f (i , zero , p) = 0#
  shift₂ f (i , suc j , p) = f (i , j , cong pred (sym +'-right-suc >=> p))
