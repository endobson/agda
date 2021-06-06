{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.nat where

open import base
open import order
open import nat.order as no

instance
  LinearOrderStr-ℕ : LinearOrderStr Nat ℓ-zero
  LinearOrderStr-ℕ = record
    { _<_ = no._<_
    ; isProp-< = \x y -> no.isProp≤ {suc x} {y}
    ; irrefl-< = \{x} -> no.same-≮ {x}
    ; trans-< = \{x} {y} {z} -> no.trans-< {x} {y} {z}
    ; connected-< = no.connected-nat<
    ; comparison-< = no.comparison-nat<
    }

  TotalOrderStr-ℕ : TotalOrderStr Nat ℓ-zero
  TotalOrderStr-ℕ = record
    { _≤_ = no._≤_
    ; isProp-≤ = \x y -> no.isProp≤ {x} {y}
    ; refl-≤ = \{x} -> no.same-≤ x
    ; trans-≤ = \{x} {y} {z} -> no.trans-≤ {x} {y} {z}
    ; antisym-≤ = ≤-antisym
    ; connex-≤ = no.connex-≤
    }
