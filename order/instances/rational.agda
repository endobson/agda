{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import base
open import order
open import rational
import rational.order as ro

open ro public using
 ( LinearOrderStr-ℚ
 ; DecidableLinearOrderStr-ℚ
 ; TotalOrderStr-ℚ
 )

instance
  CompatibleOrderStr-ℚ :
    CompatibleOrderStr ℚ ℓ-zero ℓ-zero LinearOrderStr-ℚ TotalOrderStr-ℚ
  CompatibleOrderStr-ℚ = record
    { weaken-< = \{x} {y} -> ro.weaken-ℚ< {x} {y}
    ; strengthen-≤-≠ = ro.strengthen-ℚ≤-≠
    }
