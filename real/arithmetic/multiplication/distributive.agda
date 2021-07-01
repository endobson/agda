{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication.distributive where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import rational.proper-interval
open import rational.proper-interval.multiplication-assoc
open import rational.proper-interval.multiplication-distributive
open import real
open import relation hiding (U)
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.associative
open import real.arithmetic
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation
open import univalence


private
  module _ (x y : ℝ) where
    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

ℝ∈Iℚ-+ : (x y : ℝ) (a b : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ y b -> ℝ∈Iℚ (x ℝ+ y) (a i+ b)
ℝ∈Iℚ-+ x y a b (xl-a , xu-a) (yl-b , yu-b) =
  ∣ Iℚ.l a , Iℚ.l b , xl-a , yl-b , refl ∣ ,
  ∣ Iℚ.u a , Iℚ.u b , xu-a , yu-b , refl ∣


ℝ∈Iℚ-⊆ : (x : ℝ) {a b : Iℚ} -> a i⊆ b -> ℝ∈Iℚ x a -> ℝ∈Iℚ x b
ℝ∈Iℚ-⊆ x {a} {b} (i⊆-cons bl≤al au≤bu) (xl-a , xu-a) =
  isLowerSet≤ x _ _ bl≤al xl-a , isUpperSet≤ x _ _ au≤bu xu-a


module _ (x y z : ℝ)
  where
  private
    module x = Real x
    module y = Real y
    module z = Real z
    xy = x ℝ+ y
    xyz = xy ℝ* z
    xz = x ℝ* z
    yz = y ℝ* z
    xzyz = xz ℝ+ yz

    module xy = Real xy
    module xyz = Real xyz
    module xz = Real xz
    module yz = Real yz
    module xyxz = Real xzyz

    forward : (q : Iℚ) -> ℝ∈Iℚ xzyz q -> ℝ∈Iℚ xyz q
    forward q xzyz∈q =
      unsquash (isProp-ℝ∈Iℚ xyz q) (∥-map2 handle (fst xzyz∈q) (snd xzyz∈q))
      where
      ql = Iℚ.l q
      qu = Iℚ.u q
      handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xz.L a × yz.L b × a r+ b == ql) ->
               Σ[ c ∈ ℚ ] Σ[ d ∈ ℚ ] (xz.U c × yz.U d × c r+ d == qu) -> ℝ∈Iℚ xyz q
      handle (a , b , xz-la , yz-lb , ab-path) (c , d , xz-uc , yz-ud , cd-path) =
        unsquash (isProp-ℝ∈Iℚ xyz q) (∥-map4 handle2 xz-la yz-lb xz-uc yz-ud)
        where

        ac = Iℚ-cons a c (inj-l (ℝ-bounds->ℚ< xz a c xz-la xz-uc))
        bd = Iℚ-cons b d (inj-l (ℝ-bounds->ℚ< yz b d yz-lb yz-ud))
        ac+bd=q : ac i+ bd == q
        ac+bd=q = Iℚ-bounds-path ab-path cd-path

        handle2 : L' x z a -> L' y z b -> U' x z c -> U' y z d -> ℝ∈Iℚ xyz q
        handle2 (xa , za , exa , eza , a≤) (yb , zb , eyb , ezb , b≤)
                (xc , zc , exc , ezc , ≤c) (yd , zd , eyd , ezd , ≤d) =
          ℝ∈Iℚ-⊆ xyz xiyizi⊆q xyz∈[xiyi]zi
          where
          o-xaxc = ℝ∈Iℚ->Overlap x xa xc exa exc
          xi = i-intersect xa xc o-xaxc
          x∈xi = ℝ∈Iℚ-intersect x xa xc exa exc

          o-ybyd = ℝ∈Iℚ->Overlap y yb yd eyb eyd
          yi = i-intersect yb yd o-ybyd
          y∈yi = ℝ∈Iℚ-intersect y yb yd eyb eyd

          o-zazc = ℝ∈Iℚ->Overlap z za zc eza ezc
          zi1 = i-intersect za zc o-zazc
          z∈zi1 = ℝ∈Iℚ-intersect z za zc eza ezc

          o-zbzd = ℝ∈Iℚ->Overlap z zb zd ezb ezd
          zi2 = i-intersect zb zd o-zbzd
          z∈zi2 = ℝ∈Iℚ-intersect z zb zd ezb ezd

          o-zi1zi2 = ℝ∈Iℚ->Overlap z zi1 zi2 z∈zi1 z∈zi2
          zi = i-intersect zi1 zi2 o-zi1zi2
          z∈zi = ℝ∈Iℚ-intersect z zi1 zi2 z∈zi1 z∈zi2

          xi⊆xa = i-intersect-⊆₁ xa xc o-xaxc
          xi⊆xc = i-intersect-⊆₂ xa xc o-xaxc
          zi1⊆za = i-intersect-⊆₁ za zc o-zazc
          zi1⊆zc = i-intersect-⊆₂ za zc o-zazc

          yi⊆yb = i-intersect-⊆₁ yb yd o-ybyd
          yi⊆yd = i-intersect-⊆₂ yb yd o-ybyd
          zi2⊆zb = i-intersect-⊆₁ zb zd o-zbzd
          zi2⊆zd = i-intersect-⊆₂ zb zd o-zbzd

          zi⊆zi1 = i-intersect-⊆₁ zi1 zi2 o-zi1zi2
          zi⊆zi2 = i-intersect-⊆₂ zi1 zi2 o-zi1zi2

          zi⊆za = trans-i⊆ zi⊆zi1 zi1⊆za
          zi⊆zc = trans-i⊆ zi⊆zi1 zi1⊆zc
          zi⊆zb = trans-i⊆ zi⊆zi2 zi2⊆zb
          zi⊆zd = trans-i⊆ zi⊆zi2 zi2⊆zd

          xizi⊆xaza = i*-preserves-⊆ xi⊆xa zi⊆za
          xizi⊆xczc = i*-preserves-⊆ xi⊆xc zi⊆zc
          yizi⊆ybzb = i*-preserves-⊆ yi⊆yb zi⊆zb
          yizi⊆ydzd = i*-preserves-⊆ yi⊆yd zi⊆zd

          xizi⊆ac : (xi i* zi) i⊆ ac
          xizi⊆ac = i⊆-cons (i⊆-Lower xizi⊆xaza a a≤) (i⊆-Upper xizi⊆xczc c ≤c)
          yizi⊆bd : (yi i* zi) i⊆ bd
          yizi⊆bd = i⊆-cons (i⊆-Lower yizi⊆ybzb b b≤) (i⊆-Upper yizi⊆ydzd d ≤d)

          xiziyizi⊆acbd = i+-preserves-⊆ xizi⊆ac yizi⊆bd
          xiziyizi⊆q = subst (((xi i* zi) i+ (yi i* zi)) i⊆_) ac+bd=q xiziyizi⊆acbd
          xiyizi⊆q = trans-i⊆ (i*-distrib-i+-right xi yi zi) xiziyizi⊆q


          xyz∈[xiyi]zi : ℝ∈Iℚ xyz ((xi i+ yi) i* zi)
          xyz∈[xiyi]zi = ℝ∈Iℚ-* xy z (xi i+ yi) zi (ℝ∈Iℚ-+ x y xi yi x∈xi y∈yi) z∈zi


  abstract
    ℝ*-distrib-ℝ+-right : xyz == xzyz
    ℝ*-distrib-ℝ+-right = sym (ℝ∈Iℚ->path xzyz xyz forward)
