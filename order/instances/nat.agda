{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.nat where

open import base
open import nat.order as no
open import order
open import relation

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

private
  trichotomous-ℕ< : Trichotomous _<_
  trichotomous-ℕ< x y = handle (decide-nat< x y) (decide-nat< y x)
    where
    handle : Dec (x < y) -> Dec (y < x) -> Tri< x y
    handle (yes x<y) _         = tri<' x<y
    handle (no x≮y)  (yes y<x) = tri>' y<x
    handle (no x≮y)  (no y≮x)  = tri=' (connected-< x≮y y≮x)

instance
  DecidableLinearOrderStr-ℕ : DecidableLinearOrderStr LinearOrderStr-ℕ
  DecidableLinearOrderStr-ℕ = record
    { trichotomous-< = trichotomous-ℕ<
    }
