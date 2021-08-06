{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import base
open import order
open import rational
import rational.order as ro

open ro public using
 ( LinearOrderStr-ℚ
 )

instance
  TotalOrderStr-ℚ : TotalOrderStr ℚ ℓ-zero
  TotalOrderStr-ℚ = record
    { _≤_ = ro._ℚ≤_
    ; isProp-≤ = \x y -> ro.isProp-ℚ≤ {x} {y}
    ; refl-≤ = ro.refl-ℚ≤
    ; trans-≤ = \{a} {b} {c} -> ro.trans-ℚ≤ {a} {b} {c}
    ; antisym-≤ = ro.antisym-ℚ≤
    ; connex-≤ = ro.connex-ℚ≤
    }


  DecidableCompatibleOrderStr-ℚ :
    DecidableCompatibleOrderStr ℚ ℓ-zero ℓ-zero LinearOrderStr-ℚ TotalOrderStr-ℚ
  DecidableCompatibleOrderStr-ℚ = record
    { split-< = ro.split-ℚ<
    }
