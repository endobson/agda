{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import rational.order public using
 ( isLinearOrder-ℚ<
 ; DecidableLinearOrderStr-ℚ
 ; isPartialOrder-ℚ≤
 ; TotalOrderStr-ℚ
 ; CompatibleOrderStr-ℚ
 )
