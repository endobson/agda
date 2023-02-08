{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.int where

open import base
open import int
open import order
open import relation
open import truncation

import int.order as io

instance
  LinearOrderStr-ℤ : LinearOrderStr ℤ ℓ-zero
  LinearOrderStr-ℤ = record
    { _<_ = io._<_
    ; isLinearOrder-< = record
      { isProp-< = io.isProp-<
      ; irrefl-< = \{x} -> io.irrefl-< {x}
      ; trans-< = \{x} {y} {z} -> io.trans-< {x} {y} {z}
      ; connected-< = io.connected-<
      ; comparison-< = \i j k i<k -> ∣ io.comparison-< i<k j ∣
      }
    }


instance
  PartialOrderStr-ℤ : PartialOrderStr ℤ ℓ-zero
  PartialOrderStr-ℤ = record
    { _≤_ = io._≤_
    ; isPartialOrder-≤ = record
      { isProp-≤ = io.isProp-≤
      ; refl-≤ = \{x} -> io.refl-≤ {x}
      ; trans-≤ = \{x} {y} {z} -> io.trans-≤ {x} {y} {z}
      ; antisym-≤ = io.antisym-≤
      }
    }

private
  trichotomous-ℤ< : Trichotomous io._<_
  trichotomous-ℤ< i j = handle (io.split-< i j) (io.split-< j i)
    where
    handle : (i < j ⊎ j io.≤ i) -> (j < i ⊎ i io.≤ j) -> Tri (i < j) (i == j) (j < i)
    handle (inj-l i<j) _           = tri<' i<j
    handle (inj-r j≤i) (inj-l j<i) = tri>' j<i
    handle (inj-r j≤i) (inj-r i≤j) = tri=' (io.antisym-≤ i≤j j≤i)

instance
  DecidableLinearOrderStr-ℤ : DecidableLinearOrderStr LinearOrderStr-ℤ
  DecidableLinearOrderStr-ℤ = record
    { trichotomous-< = trichotomous-ℤ<
    }
