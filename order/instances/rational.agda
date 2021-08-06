{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import base
open import order
open import rational
import rational.order as ro

instance
  LinearOrderStr-ℚ : LinearOrderStr ℚ ℓ-zero
  LinearOrderStr-ℚ = record
    { _<_ = ro._<_
    ; isProp-< = \x y -> ro.isProp-< {x} {y}
    ; irrefl-< = \{x} -> ro.irrefl-< {x}
    ; trans-< = \{x} {y} {z} -> ro.trans-< {x} {y} {z}
    ; connected-< = ro.connected-<
    ; comparison-< = ro.comparison-<
    }

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
    { split-< = ro.split-<
    }
