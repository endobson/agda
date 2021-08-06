{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication.associative where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import rational
open import rational.order
open import rational.minmax
open import rational.proper-interval
open import rational.proper-interval.multiplication-assoc
open import real
open import relation hiding (U)
open import real.arithmetic.multiplication
open import real.interval
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



module _ (x y z : ℝ)
  where
  private
    module x = Real x
    module y = Real y
    module z = Real z
    xy = x ℝ*ᵉ y
    xy-z = xy ℝ*ᵉ z
    yz = y ℝ*ᵉ z
    x-yz = x ℝ*ᵉ yz

    module xy = Real xy
    module xy-z = Real xy-z
    module yz = Real yz
    module x-yz = Real x-yz


    forward : (q : Iℚ) -> ℝ∈Iℚ xy-z q -> ℝ∈Iℚ x-yz q
    forward q xy-z∈q =
        unsquash (isProp-ℝ∈Iℚ x-yz q) (∥-map2 handle (fst xy-z∈q) (snd xy-z∈q))
      where
      ql = Iℚ.l q
      qu = Iℚ.u q
      handle : L' xy z ql -> U' xy z qu -> ℝ∈Iℚ x-yz q
      handle (a1 , b1 , xy∈a1 , z∈b1 , ql≤a1b1)
            (a2 , b2 , xy∈a2 , z∈b2 , a2b2≤qu) =
        unsquash (isProp-ℝ∈Iℚ x-yz q) (∥-map2 handle2 (fst xy∈a) (snd xy∈a))
        where
        o-a1a2 = ℝ∈Iℚ->Overlap xy a1 a2 xy∈a1 xy∈a2
        a = i-intersect a1 a2 o-a1a2
        xy∈a = ℝ∈Iℚ-intersect xy a1 a2 xy∈a1 xy∈a2

        o-b1b2 = ℝ∈Iℚ->Overlap z b1 b2 z∈b1 z∈b2
        b = i-intersect b1 b2 o-b1b2
        z∈b = ℝ∈Iℚ-intersect z b1 b2 z∈b1 z∈b2

        al = Iℚ.l a
        au = Iℚ.u a
        bl = Iℚ.l b
        bu = Iℚ.u b

        a⊆a1 = i-intersect-⊆₁ a1 a2 o-a1a2
        a⊆a2 = i-intersect-⊆₂ a1 a2 o-a1a2
        b⊆b1 = i-intersect-⊆₁ b1 b2 o-b1b2
        b⊆b2 = i-intersect-⊆₂ b1 b2 o-b1b2

        ab⊆a1b1 = i*-preserves-⊆ a⊆a1 b⊆b1
        ab⊆a2b2 = i*-preserves-⊆ a⊆a2 b⊆b2

        q-lower-1 : i-Lower (a1 i* b1) ql
        q-lower-1 = ql≤a1b1

        handle2 : L' x y al -> U' x y au -> ℝ∈Iℚ x-yz q
        handle2 (c1 , d1 , x∈c1 , y∈d1 , al≤c1d1)
                (c2 , d2 , x∈c2 , y∈d2 , c2d2≤au) =
          ∣ (c , (d i* b) , x∈c , ℝ∈Iℚ-*ᵉ y z d b y∈d z∈b , q-lower) ∣ ,
          ∣ (c , (d i* b) , x∈c , ℝ∈Iℚ-*ᵉ y z d b y∈d z∈b , q-upper) ∣

          where
          o-c1c2 = ℝ∈Iℚ->Overlap x c1 c2 x∈c1 x∈c2
          c = i-intersect c1 c2 o-c1c2
          x∈c = ℝ∈Iℚ-intersect x c1 c2 x∈c1 x∈c2

          o-d1d2 = ℝ∈Iℚ->Overlap y d1 d2 y∈d1 y∈d2
          d = i-intersect d1 d2 o-d1d2
          y∈d = ℝ∈Iℚ-intersect y d1 d2 y∈d1 y∈d2

          c⊆c1 = i-intersect-⊆₁ c1 c2 o-c1c2
          c⊆c2 = i-intersect-⊆₂ c1 c2 o-c1c2
          d⊆d1 = i-intersect-⊆₁ d1 d2 o-d1d2
          d⊆d2 = i-intersect-⊆₂ d1 d2 o-d1d2

          cd⊆c1d1 = i*-preserves-⊆ c⊆c1 d⊆d1
          cd⊆c2d2 = i*-preserves-⊆ c⊆c2 d⊆d2

          cd⊆a : (c i* d) i⊆ a
          cd⊆a = i⊆-cons (i⊆-Lower cd⊆c1d1 al al≤c1d1) (i⊆-Upper cd⊆c2d2 au c2d2≤au)

          c-db=cd-b : c i* (d i* b) == (c i* d) i* b
          c-db=cd-b = i*-assoc c d b

          c-db⊆a1b1 : (c i* (d i* b)) i⊆ (a1 i* b1)
          c-db⊆a1b1 =
            subst (_i⊆ (a1 i* b1)) (sym c-db=cd-b)
                  (trans-i⊆ (i*₂-preserves-⊆ cd⊆a b) ab⊆a1b1)

          c-db⊆a2b2 : (c i* (d i* b)) i⊆ (a2 i* b2)
          c-db⊆a2b2 =
            subst (_i⊆ (a2 i* b2)) (sym c-db=cd-b)
                  (trans-i⊆ (i*₂-preserves-⊆ cd⊆a b) ab⊆a2b2)

          q-lower : i-Lower (c i* (d i* b)) ql
          q-lower = i⊆-Lower c-db⊆a1b1 ql ql≤a1b1

          q-upper : i-Upper (c i* (d i* b)) qu
          q-upper = i⊆-Upper c-db⊆a2b2 qu a2b2≤qu

    ℝ*ᵉ-assoc : xy-z == x-yz
    ℝ*ᵉ-assoc = ℝ∈Iℚ->path xy-z x-yz forward

  abstract
    ℝ*-assoc : (x ℝ* y) ℝ* z == x ℝ* (y ℝ* z)
    ℝ*-assoc = cong (_ℝ* z) (ℝ*-eval {x} {y}) >=> (ℝ*-eval {xy} {z}) >=>
               ℝ*ᵉ-assoc >=>
               sym (ℝ*-eval {x} {yz}) >=> sym (cong (x ℝ*_) (ℝ*-eval {y} {z}))
