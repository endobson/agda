{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import rational.order public using
 ( LinearOrderStr-ℚ
 ; DecidableLinearOrderStr-ℚ
 ; PartialOrderStr-ℚ
 ; TotalOrderStr-ℚ
 ; CompatibleOrderStr-ℚ
 )
