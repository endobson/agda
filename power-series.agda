{-# OPTIONS --cubical --safe --exact-split #-}

module power-series where

open import base
open import hlevel
open import nat

module _ {ℓD : Level} (D : Type ℓD) where
  record PowerSeries : Type ℓD where
    constructor power-series
    field
      seq : ℕ -> D

opaque
  isSet-PowerSeries : {ℓD : Level} {D : Type ℓD} -> isSet D -> isSet (PowerSeries D)
  isSet-PowerSeries isSet-D (power-series s1) (power-series s2) p1 p2 i j =
     power-series
       (isSetΠ (\_ -> isSet-D) s1 s2
        (\i -> PowerSeries.seq (p1 i))
        (\i -> PowerSeries.seq (p2 i)) i j)

PowerSeries-path : {ℓD : Level} {D : Type ℓD} {p1 p2 : PowerSeries D} ->
                   ((n : ℕ) -> PowerSeries.seq p1 n == PowerSeries.seq p2 n) -> p1 == p2
PowerSeries-path p i = power-series (\n -> p n i)
