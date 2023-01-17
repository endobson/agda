{-# OPTIONS --cubical --safe --exact-split #-}

module order.flipped where

open import base
open import order
open import sum
open import truncation

LinearOrderStr-Flipped :
  {ℓA ℓ< : Level} {A : Type ℓA} -> LinearOrderStr A ℓ< -> LinearOrderStr A ℓ<
LinearOrderStr-Flipped o = record
  { _<_ = \x y -> y o.< x
  ; isProp-< = o.isProp-<
  ; irrefl-< = o.irrefl-<
  ; trans-< = \lt1 lt2 -> (o.trans-< lt2 lt1)
  ; connected-< = \ ¬lt1 ¬lt2 -> o.connected-< ¬lt2 ¬lt1
  ; comparison-< = \a b c lt -> ∥-map ⊎-swap (o.comparison-< c b a lt)
  }
  where
  module o = LinearOrderStr o

PartialOrderStr-Flipped :
  {ℓA ℓ≤ : Level} {A : Type ℓA} -> PartialOrderStr A ℓ≤ -> PartialOrderStr A ℓ≤
PartialOrderStr-Flipped o = record
  { _≤_ = \x y -> y o.≤ x
  ; isProp-≤ = o.isProp-≤
  ; refl-≤ = o.refl-≤
  ; trans-≤ = \lt1 lt2 -> (o.trans-≤ lt2 lt1)
  ; antisym-≤ = \lt1 lt2 -> o.antisym-≤ lt2 lt1
  }
  where
  module o = PartialOrderStr o

TotalOrderStr-Flipped :
  {ℓA ℓ≤ : Level} {A : Type ℓA} {PO : PartialOrderStr A ℓ≤} ->
  TotalOrderStr PO -> TotalOrderStr (PartialOrderStr-Flipped PO)
TotalOrderStr-Flipped o = record { connex-≤ = \lt1 lt2 -> o.connex-≤ lt2 lt1 }
  where
  module o = TotalOrderStr o
