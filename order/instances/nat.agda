{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.nat where

open import base
open import order
open import nat.order as no

instance
  LinearOrderStr-ℕ : LinearOrderStr Nat ℓ-zero
  LinearOrderStr-ℕ = record
    { _<_ = no._<_
    ; isProp-< = no.isProp≤
    ; irrefl-< = \{x} -> no.same-≮ {x}
    ; trans-< = \{x} {y} {z} -> no.trans-< {x} {y} {z}
    ; connected-< = no.connected-nat<
    ; comparison-< = no.comparison-nat<
    }

  PartialOrderStr-ℕ : PartialOrderStr Nat ℓ-zero
  PartialOrderStr-ℕ = record
    { _≤_ = no._≤_
    ; isProp-≤ = no.isProp≤
    ; refl-≤ = \{x} -> no.same-≤ x
    ; trans-≤ = \{x} {y} {z} -> no.trans-≤ {x} {y} {z}
    ; antisym-≤ = ≤-antisym
    }
  TotalOrderStr-ℕ : TotalOrderStr PartialOrderStr-ℕ
  TotalOrderStr-ℕ = record
    { connex-≤ = no.connex-≤
    }
