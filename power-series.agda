{-# OPTIONS --cubical --safe --exact-split #-}

module power-series where

open import base
open import nat
open import equality
open import hlevel
open import additive-group
open import funext

module _ {ℓD : Level} (D : Type ℓD) where

  record PowerSeries : Type ℓD where
    constructor power-series
    field
      seq : ℕ -> D


module _ {ℓD : Level} {D : Type ℓD} where
  abstract
    isSet-PowerSeries : isSet D -> isSet (PowerSeries D)
    isSet-PowerSeries isSet-D (power-series s1) (power-series s2) p1 p2 i j =
       power-series
         (isSetΠ (\_ -> isSet-D) s1 s2
          (\i -> PowerSeries.seq (p1 i))
          (\i -> PowerSeries.seq (p2 i)) i j)

  instance
    AdditiveCommMonoid-PS : {{ACM : AdditiveCommMonoid D}} -> AdditiveCommMonoid (PowerSeries D)
    AdditiveCommMonoid-PS {{ACM}} = record
      { comm-monoid = record
        { monoid = record
          { ε = 0-PS
          ; _∙_ = +-PS
          ; ∙-assoc = +-PS-assoc
          ; ∙-left-ε = +-PS-left-zero
          ; ∙-right-ε = +-PS-right-zero
          ; isSet-Domain = isSet-PowerSeries (AdditiveCommMonoid.isSet-Domain ACM)
          }
        ; ∙-commute = +-PS-commute
        }
      }
      where
      0-PS : PowerSeries D
      0-PS = power-series (\_ -> 0#)
      +-PS : PowerSeries D -> PowerSeries D -> PowerSeries D
      +-PS (power-series x) (power-series y) = power-series (\i -> x i + y i)

      abstract
        +-PS-assoc : {a b c : PowerSeries D} -> (+-PS (+-PS a b) c) == (+-PS a (+-PS b c))
        +-PS-assoc {power-series sa} {power-series sb} {power-series sc} j =
          power-series (\i -> +-assocᵉ (sa i) (sb i) (sc i) j)
        +-PS-left-zero : {a : PowerSeries D} -> (+-PS 0-PS a) == a
        +-PS-left-zero {power-series s} j = power-series (\i -> +-left-zeroᵉ (s i) j)
        +-PS-right-zero : {a : PowerSeries D} -> (+-PS a 0-PS) == a
        +-PS-right-zero {power-series s} j = power-series (\i -> +-right-zeroᵉ (s i) j)
        +-PS-commute : {a b : PowerSeries D} -> (+-PS a b) == (+-PS b a)
        +-PS-commute {power-series sa} {power-series sb} j =
          power-series (\i -> +-commuteᵉ (sa i) (sb i) j)
