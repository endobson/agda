{-# OPTIONS --cubical --safe --exact-split #-}

module order.flipped where

open import base
open import order
open import relation
open import sum
open import truncation

LinearOrderStr-Flipped :
  {ℓA ℓ< : Level} {A : Type ℓA} {A< : Rel A ℓ<} -> isLinearOrder A< -> isLinearOrder (\x y -> A< y x)
LinearOrderStr-Flipped LO = record
  { isProp-< = isProp-<
  ; irrefl-< = irrefl-<
  ; trans-< = \lt1 lt2 -> trans-< lt2 lt1
  ; connected-< = \ ¬lt1 ¬lt2 -> connected-< ¬lt2 ¬lt1
  ; comparison-< = \a b c lt -> ∥-map ⊎-swap (comparison-< c b a lt)
  }
  where
  instance
    ILO = LO

PartialOrderStr-Flipped :
  {ℓA ℓ≤ : Level} {A : Type ℓA} {A≤ : Rel A ℓ≤} -> isPartialOrder A≤ -> isPartialOrder (\x y -> A≤ y x)
PartialOrderStr-Flipped PO = record
  { isProp-≤ = isProp-≤
  ; refl-≤ = refl-≤
  ; trans-≤ = \lt1 lt2 -> trans-≤ lt2 lt1
  ; antisym-≤ = \lt1 lt2 -> antisym-≤ lt2 lt1
  }
  where
  instance
    IPO = PO

TotalOrderStr-Flipped :
  {ℓA ℓ≤ : Level} {A : Type ℓA} {A≤ : Rel A ℓ≤} {PO : isPartialOrder A≤} ->
  TotalOrderStr PO -> TotalOrderStr (PartialOrderStr-Flipped PO)
TotalOrderStr-Flipped o = record { connex-≤ = \lt1 lt2 -> o.connex-≤ lt2 lt1 }
  where
  module o = TotalOrderStr o
