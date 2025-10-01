{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.area.raw where

open import base
open import finsum
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box

boxes-raw-area : {ℓ : Level} -> Boxes ℓ -> ℚ
boxes-raw-area b = finiteSumᵉ (Boxes.Index b) (\i -> Box.area (Boxes.box b i))
