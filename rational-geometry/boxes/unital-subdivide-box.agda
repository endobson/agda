{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.unital-subdivide-box where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import fin
open import finset
open import finset.instances
open import finset.instances.sigma
open import int
open import int.add1
open import int.addition
open import int.base
open import int.nat
open import int.order
open import int.sign
open import nat
open import nat.order
open import order
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.int
open import ordered-semiring
open import rational
open import rational-geometry.boxes.area.raw
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.subdivide-box
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import rational.quotient
open import ring
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.natural-reciprocal
open import sigma.base
open import truncation

opaque
  subdivide-boxΣ :
    (u : ℚ⁺) (b : Box) -> isGridAlignedBox u b ->
    Σ[ B ∈ Boxes ℓ-zero ] (
      isGridAlignedBoxes u B ×
      isUnitalBoxes u B ×
      Boxes.region B == Box.region b ×
      boxes-raw-area B == Box.area b ×
      hasNoOverlap B)
  subdivide-boxΣ u⁺@(u , 0<u) b g@((gln , glp) , (grn , grp) , (gbn , gbp) , (gtn , gtp)) =
    B ,
    isGridAligned-B ,
    isUnital-B ,
    subdivide-Box-same-Region b xn yn ,
    subdivide-Box-same-raw-area b xn yn ,
    hasNoOverlap-subdivide-Box b xn yn
    where
    xnℤ : ℤ
    xnℤ = diff gln grn
    xnℤ-path : (diff (Box.left b) (Box.right b)) == ℤ->ℚ xnℤ * u
    xnℤ-path =
      cong2 diff (sym glp) (sym grp) >=>
      sym *-distrib-diff-right >=>
      *-left (sym (ℤ->ℚ-preserves-diff _ _))
    0<xnℤ : 0# < xnℤ
    0<xnℤ =
      ℤ->ℚ-reflects-< _ _
        (*₂-reflects-0<
          (trans-<-= (diff-0<⁺ (Box.left<right b)) xnℤ-path)
          (asym-< 0<u))

    xn : Nat⁺
    xn = abs' xnℤ , Pos'-abs' (inj-l 0<xnℤ)
    xn-path : (diff (Box.left b) (Box.right b)) * 1/ℕ xn == u
    xn-path =
      *-left xnℤ-path >=>
      *-commute >=>
      sym *-assoc >=>
      *-left (*-right (cong ℤ->ℚ (nonneg-abs' (weaken-< 0<xnℤ))) >=> 1/ℕ-ℕ-path xn) >=>
      *-left-one

    ynℤ : ℤ
    ynℤ = diff gbn gtn
    ynℤ-path : (diff (Box.bottom b) (Box.top b)) == ℤ->ℚ ynℤ * u
    ynℤ-path =
      cong2 diff (sym gbp) (sym gtp) >=>
      sym *-distrib-diff-right >=>
      *-left (sym (ℤ->ℚ-preserves-diff _ _))
    0<ynℤ : 0# < ynℤ
    0<ynℤ =
      ℤ->ℚ-reflects-< _ _
        (*₂-reflects-0<
          (trans-<-= (diff-0<⁺ (Box.bottom<top b)) ynℤ-path)
          (asym-< 0<u))

    yn : Nat⁺
    yn = abs' ynℤ , Pos'-abs' (inj-l 0<ynℤ)
    yn-path : (diff (Box.bottom b) (Box.top b)) * 1/ℕ yn == u
    yn-path =
      *-left ynℤ-path >=>
      *-commute >=>
      sym *-assoc >=>
      *-left (*-right (cong ℤ->ℚ (nonneg-abs' (weaken-< 0<ynℤ))) >=> 1/ℕ-ℕ-path yn) >=>
      *-left-one

    B : Boxes ℓ-zero
    B = subdivide-Box b xn yn

    isUnital-B : isUnitalBoxes u⁺ B
    isUnital-B i@(ix , iy) =
      fst (subdivide-Box-side-lengths b xn yn i) >=> xn-path ,
      snd (subdivide-Box-side-lengths b xn yn i) >=> yn-path
      where
      bᵢ : Box
      bᵢ = Boxes.box B i

    isGridAligned-B : isGridAlignedBoxes u⁺ B
    isGridAligned-B i@(ix , iy) =
      x-aligned (ℕ->ℤ (Fin.i ix)) ,
      x-aligned (ℕ->ℤ (suc (Fin.i ix))) ,
      y-aligned (ℕ->ℤ (Fin.i iy)) ,
      y-aligned (ℕ->ℤ (suc (Fin.i iy)))
      where
      module bᵢ = Box (Boxes.box B i)

      x-aligned : ∀ (i : ℤ) -> isGridAlignedℚ u⁺ (Box.left b + ℤ->ℚ i * (diff (Box.left b) (Box.right b) * 1/ℕ xn))
      x-aligned i =
        isGridAlignedℚ-+ u⁺ (gln , glp) (isGridAlignedℚ-ℤ* u⁺ i (1# , *-left-one >=> sym xn-path))
      y-aligned : ∀ (i : ℤ) -> isGridAlignedℚ u⁺ (Box.bottom b + ℤ->ℚ i * (diff (Box.bottom b) (Box.top b) * 1/ℕ yn))
      y-aligned i =
        isGridAlignedℚ-+ u⁺ (gbn , gbp) (isGridAlignedℚ-ℤ* u⁺ i (1# , *-left-one >=> sym yn-path))
