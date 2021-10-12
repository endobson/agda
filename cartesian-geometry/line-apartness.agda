{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.line-apartness where

open import apartness
open import base
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction.apartness
open import cartesian-geometry.vector
open import functions

private

  data Line# (l1 l2 : Line) : Type₁ where
    line#-sd-case : (line-semi-direction l1 # line-semi-direction l2) -> Line# l1 l2
    line#-point-case : ((p1 p2 : Point) -> ⟨ OnLine l1 p1 ⟩ -> ⟨ OnLine l2 p2 ⟩ -> p1 # p2) -> Line# l1 l2

  sym-Line# : {l1 l2 : Line} -> Line# l1 l2 -> Line# l2 l1
  sym-Line# (line#-sd-case ap) = line#-sd-case (sym-# ap)
  sym-Line# (line#-point-case ap) =
    line#-point-case (\p1 p2 o1 o2 -> sym-# (ap p2 p1 o2 o1))

  -- tight-Line# : {l1 l2 : Line} -> ¬ (Line# l1 l2) -> l1 == l2
  -- tight-Line# {l1} {l2} ¬ap = ?
  --   where
  --   sd1 = line-semi-direction l1
  --   sd2 = line-semi-direction l2
  --   sd1=sd2 : sd1 == sd2
  --   sd1=sd2 = tight-# (¬ap ∘ line#-sd-case)
