{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.int where

open import base
open import equality
open import int
open import order
open import relation
open import truncation

import int.order as io

instance
  isLinearOrder-ℤ< : isLinearOrder io._<_
  isLinearOrder-ℤ< = record
    { isProp-< = io.isProp-<
    ; irrefl-< = \{x} -> io.irrefl-< {x}
    ; trans-< = \{x} {y} {z} -> io.trans-< {x} {y} {z}
    ; connected-< = io.connected-<
    ; comparison-< = \i j k i<k -> ∣ io.comparison-< i<k j ∣
    }

  isPartialOrder-ℤ≤ : isPartialOrder io._≤_
  isPartialOrder-ℤ≤ = record
    { isProp-≤ = io.isProp-≤
    ; refl-≤ = \{x} -> io.refl-≤ {x}
    ; trans-≤ = \{x} {y} {z} -> io.trans-≤ {x} {y} {z}
    ; antisym-≤ = io.antisym-≤
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
  DecidableLinearOrderStr-ℤ : DecidableLinearOrderStr useⁱ
  DecidableLinearOrderStr-ℤ = record
    { trichotomous-< = trichotomous-ℤ<
    }


private
  weaken-ℤ< : {m n : ℤ} -> (m < n) -> m ≤ n
  weaken-ℤ< ((i , _) , p) = (i , p)

  convert-ℤ≮ : {m n : ℤ} -> ¬ (m < n) -> n ≤ m
  convert-ℤ≮ {m} {n} m≮n = case (trichotomous-< m n) of
    \{ (tri< m<n _ _) -> bot-elim (m≮n m<n)
     ; (tri= _ m=n _) -> path-≤ (sym m=n)
     ; (tri> _ _ m>n) -> weaken-ℤ< m>n
     }

instance
  CompatibleOrderStr-ℤ : CompatibleOrderStr useⁱ useⁱ
  CompatibleOrderStr-ℤ = record
    { convert-≮ = convert-ℤ≮
    }
