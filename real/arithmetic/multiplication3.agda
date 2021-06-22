{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication3 where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import rational.minmax
open import rational.proper-interval
open import real
open import real.sequence
open import real.arithmetic.absolute-value
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

module _ (x y : ℝ)
  where
  private
    module x = Real x
    module y = Real y

    ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
    ℝ∈Iℚ z (Iℚ-cons l u _) = Real.L z l × Real.U z u

    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

    ℝ∈Iℚ->Overlap : (z : ℝ) (a b : Iℚ) -> ℝ∈Iℚ z a -> ℝ∈Iℚ z b -> Overlap a b
    ℝ∈Iℚ->Overlap z a b (al , au) (bl , bu) =
      inj-l (ℝ-bounds->ℚ< z _ _ bl au) , inj-l (ℝ-bounds->ℚ< z _ _ al bu)

    ℝ∈Iℚ-intersect : (z : ℝ) (a b : Iℚ) -> (ea : ℝ∈Iℚ z a) -> (eb : ℝ∈Iℚ z b) ->
                     ℝ∈Iℚ z (i-intersect a b (ℝ∈Iℚ->Overlap z a b ea eb))
    ℝ∈Iℚ-intersect z a b (al , au) (bl , bu) =
      maxℚ-property {P = Real.L z} _ _ al bl ,
      minℚ-property {P = Real.U z} _ _ au bu

    ℝ∈Iℚ->¬Constant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> ¬ (ConstantI a)
    ℝ∈Iℚ->¬Constant z a (al , au) p =
      Real.disjoint z (Iℚ.u a) (subst (Real.L z) p al , au)

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (lq , uq) = unsquash isPropBot (∥-map2 handle lq uq)
      where
      handle : L' q -> U' q -> Bot
      handle (xi1 , yi1 , exi1 , eyi1 , l1) (xi2 , yi2 , exi2 , eyi2 , u2) =
        handle2 (i*-Constant xi3 yi3 Constant-p3)
        where
        xi3 : Iℚ
        xi3 = i-intersect xi1 xi2 (ℝ∈Iℚ->Overlap x xi1 xi2 exi1 exi2)

        yi3 : Iℚ
        yi3 = i-intersect yi1 yi2 (ℝ∈Iℚ->Overlap y yi1 yi2 eyi1 eyi2)

        xi3⊆xi1 : xi3 i⊆ xi1
        xi3⊆xi1 = i-intersect-⊆₁ _ _ _
        xi3⊆xi2 : xi3 i⊆ xi2
        xi3⊆xi2 = i-intersect-⊆₂ _ _ _
        yi3⊆yi1 : yi3 i⊆ yi1
        yi3⊆yi1 = i-intersect-⊆₁ _ _ _
        yi3⊆yi2 : yi3 i⊆ yi2
        yi3⊆yi2 = i-intersect-⊆₂ _ _ _

        p1 = xi1 i* yi1
        p2 = xi2 i* yi2
        p3 = xi3 i* yi3

        p3⊆p1 : p3 i⊆ p1
        p3⊆p1 = trans-i⊆ (i*₁-preserves-⊆ xi3 yi3⊆yi1) (i*₂-preserves-⊆ xi3⊆xi1 yi1)
        p3⊆p2 : p3 i⊆ p2
        p3⊆p2 = trans-i⊆ (i*₁-preserves-⊆ xi3 yi3⊆yi2) (i*₂-preserves-⊆ xi3⊆xi2 yi2)

        l3 : i-Lower p3 q
        l3 = i⊆-Lower p3⊆p1 q l1

        u3 : i-Upper p3 q
        u3 = i⊆-Upper p3⊆p2 q u2

        Constant-p3 : ConstantI p3
        Constant-p3 = LowerUpper->Constant {q} p3 l3 u3

        handle2 : ConstantI xi3 ⊎ ConstantI yi3 -> Bot
        handle2 (inj-l cx3) = ℝ∈Iℚ->¬Constant x xi3 (ℝ∈Iℚ-intersect x xi1 xi2 exi1 exi2) cx3
        handle2 (inj-r cy3) = ℝ∈Iℚ->¬Constant y yi3 (ℝ∈Iℚ-intersect y yi1 yi2 eyi1 eyi2) cy3
