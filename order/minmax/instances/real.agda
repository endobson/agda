{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.instances.real where

open import base
open import real
open import real.minimum
open import real.maximum
open import order.instances.real
open import order.minmax

instance
  MinOperationStr-ℝ : MinOperationStr useⁱ
  MinOperationStr-ℝ = record
    { min = minℝ
    ; min-≮-left = minℝ-≤-left _ _
    ; min-≮-right = minℝ-≤-right _ _
    ; min-greatest-< = minℝ-<-both
    }

  MaxOperationStr-ℝ : MaxOperationStr useⁱ
  MaxOperationStr-ℝ = record
    { max = maxℝ
    ; max-≮-left = maxℝ-≤-left _ _
    ; max-≮-right = maxℝ-≤-right _ _
    ; max-least-< = maxℝ-<-both
    }
