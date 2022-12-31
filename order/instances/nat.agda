{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.nat where

open import base
open import order
open import nat.order as no

instance
  LinearOrderStr-ℕ : LinearOrderStr Nat ℓ-zero
  LinearOrderStr-ℕ = record
    { _<_ = no._ℕ<_
    ; isProp-< = no.isProp-ℕ≤
    ; irrefl-< = \{x} -> no.same-≮ {x}
    ; trans-< = \{x} {y} {z} -> no.trans-ℕ< {x} {y} {z}
    ; connected-< = no.connected-nat<
    ; comparison-< = no.comparison-nat<
    }

  PartialOrderStr-ℕ : PartialOrderStr Nat ℓ-zero
  PartialOrderStr-ℕ = record
    { _≤_ = no._ℕ≤_
    ; isProp-≤ = no.isProp-ℕ≤
    ; refl-≤ = \{x} -> no.same-≤ x
    ; trans-≤ = \{x} {y} {z} -> no.trans-ℕ≤ {x} {y} {z}
    ; antisym-≤ = ℕ≤-antisym
    }
  TotalOrderStr-ℕ : TotalOrderStr PartialOrderStr-ℕ
  TotalOrderStr-ℕ = record
    { connex-≤ = no.connex-ℕ≤
    }
  CompatibleOrderStr-ℕ :
    CompatibleOrderStr LinearOrderStr-ℕ PartialOrderStr-ℕ
  CompatibleOrderStr-ℕ = record
    { weaken-< = no.weaken-ℕ<
    }
