{-# OPTIONS --cubical --safe --exact-split #-}

module real.interval where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import rational
open import rational.minmax
open import rational.proper-interval
open import real
open import truncation
open import univalence

ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
ℝ∈Iℚ z a = Real.L z (Iℚ.l a) × Real.U z (Iℚ.u a)

ℝ∈Iℚ->Overlap : (z : ℝ) (a b : Iℚ) -> ℝ∈Iℚ z a -> ℝ∈Iℚ z b -> Overlap a b
ℝ∈Iℚ->Overlap z a b (al , au) (bl , bu) =
  weaken-< (ℝ-bounds->ℚ< z _ _ bl au) , weaken-< (ℝ-bounds->ℚ< z _ _ al bu)

ℝ∈Iℚ-intersect : (z : ℝ) (a b : Iℚ) -> (ea : ℝ∈Iℚ z a) -> (eb : ℝ∈Iℚ z b) ->
                 ℝ∈Iℚ z (i-intersect a b (ℝ∈Iℚ->Overlap z a b ea eb))
ℝ∈Iℚ-intersect z a b (al , au) (bl , bu) =
  maxℚ-property {P = Real.L z} _ _ al bl ,
  minℚ-property {P = Real.U z} _ _ au bu

ℝ∈Iℚ->¬Constant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> ¬ (ConstantI a)
ℝ∈Iℚ->¬Constant z a (al , au) p =
  Real.disjoint z (Iℚ.u a) (subst (Real.L z) p al , au)

ℝ∈Iℚ->NonConstant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> NonConstantI a
ℝ∈Iℚ->NonConstant z a (al , au) = (ℝ-bounds->ℚ< z _ _ al au)

isProp-ℝ∈Iℚ : (z : ℝ) (a : Iℚ) -> isProp (ℝ∈Iℚ z a)
isProp-ℝ∈Iℚ z (Iℚ-cons l u _) = isProp× (Real.isProp-L z l) (Real.isProp-U z u)

ℝ∈Iℚ->path : (x y : ℝ) -> (f : (q : Iℚ) -> ℝ∈Iℚ x q -> ℝ∈Iℚ y q) -> x == y
ℝ∈Iℚ->path x y f = LU-paths->path x y L-path U-path
  where
  module x = Real x
  module y = Real y

  f-L : (q : ℚ) -> x.L q -> y.L q
  f-L q xl-q = unsquash (y.isProp-L q) (∥-map handle x.Inhabited-U)
    where
    handle : Σ ℚ x.U -> y.L q
    handle (r , xu-r) = fst (f xi (xl-q , xu-r))
      where
      xi = Iℚ-cons q r (weaken-< (ℝ-bounds->ℚ< x q r xl-q xu-r))

  f-U : (q : ℚ) -> x.U q -> y.U q
  f-U q xu-q = unsquash (y.isProp-U q) (∥-map handle x.Inhabited-L)
    where
    handle : Σ ℚ x.L -> y.U q
    handle (r , xl-r) = snd (f xi (xl-r , xu-q))
      where
      xi = Iℚ-cons r q (weaken-< (ℝ-bounds->ℚ< x r q xl-r xu-q))

  L-path : (q : ℚ) -> x.L q == y.L q
  L-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (x.L q) (y.L q)
    i .rightInv _ = y.isProp-L q _ _
    i .leftInv _ = x.isProp-L q _ _
    i .fun = f-L q
    i .inv yl-q = unsquash (x.isProp-L q) (∥-bind handle (y.isUpperOpen-L q yl-q))
      where
      handle : Σ[ q' ∈ ℚ ] (q < q' × y.L q') -> ∥ x.L q ∥
      handle (q' , q<q' , yl-q')  = ∥-bind handle2 (x.located q q' q<q')
        where
        handle2 : (x.L q ⊎ x.U q') -> ∥ x.L q ∥
        handle2 (inj-l xl-q) = ∣ xl-q ∣
        handle2 (inj-r xu-q') = bot-elim (y.disjoint q' (yl-q' , f-U q' xu-q'))

  U-path : (q : ℚ) -> x.U q == y.U q
  U-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (x.U q) (y.U q)
    i .rightInv _ = y.isProp-U q _ _
    i .leftInv _ = x.isProp-U q _ _
    i .fun = f-U q
    i .inv yu-q = unsquash (x.isProp-U q) (∥-bind handle (y.isLowerOpen-U q yu-q))
      where
      handle : Σ[ q' ∈ ℚ ] (q' < q × y.U q') -> ∥ x.U q ∥
      handle (q' , q'<q , yu-q')  = ∥-bind handle2 (x.located q' q q'<q)
        where
        handle2 : (x.L q' ⊎ x.U q) -> ∥ x.U q ∥
        handle2 (inj-l xl-q') = bot-elim (y.disjoint q' (f-L q' xl-q' , yu-q'))
        handle2 (inj-r xu-q) = ∣ xu-q ∣

ℝ∈Iℚ-⊆ : (x : ℝ) {a b : Iℚ} -> a i⊆ b -> ℝ∈Iℚ x a -> ℝ∈Iℚ x b
ℝ∈Iℚ-⊆ x {a} {b} (i⊆-cons bl≤al au≤bu) (xl-a , xu-a) =
  isLowerSet≤ x _ _ bl≤al xl-a , isUpperSet≤ x _ _ au≤bu xu-a

ℝ∈Iℚ-Pos : (x : ℝ) -> 0ℝ ℝ< x -> ∃[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b)
ℝ∈Iℚ-Pos x 0<x = ∥-map2 handle (x.isUpperOpen-L 0r (ℝ<->L 0r x 0<x)) x.Inhabited-U
  where
  module x = Real x
  handle : Σ[ q ∈ ℚ ] (0r < q × x.L q) -> Σ ℚ x.U -> Σ[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b)
  handle (q , 0<q , xl-q) (r , xu-q) =
    (Iℚ-cons q r (weaken-< (ℝ-bounds->ℚ< x q r xl-q xu-q))) , (xl-q , xu-q) , 0<q


ℝ∈Iℚ-Pos-⊆ : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ x a -> 0ℝ ℝ< x -> ∃[ b ∈ Iℚ ] (b i⊆ a × ℝ∈Iℚ x b × PosI b)
ℝ∈Iℚ-Pos-⊆ x a x∈a 0<x = ∥-map handle (ℝ∈Iℚ-Pos x 0<x)
  where
  module x = Real x
  handle : Σ[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b) -> Σ[ c ∈ Iℚ ] (c i⊆ a × ℝ∈Iℚ x c × PosI c)
  handle (b , x∈b , pos-b) = c , c⊆a , x∈c , pos-c
    where
    o-ab = ℝ∈Iℚ->Overlap x a b x∈a x∈b
    c = i-intersect a b o-ab
    x∈c = ℝ∈Iℚ-intersect x a b x∈a x∈b

    c⊆a = i-intersect-⊆₁ a b o-ab
    c⊆b = i-intersect-⊆₂ a b o-ab
    pos-c = i⊆-preserves-PosI c⊆b pos-b
