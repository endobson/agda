{-# OPTIONS --cubical --safe --exact-split #-}

module real.order where

open import apartness
open import base
open import equality
open import functions
open import hlevel
open import isomorphism
open import order
open import rational
open import order.instances.rational
open import real
open import relation hiding (U)
open import truncation
open import univalence

record _ℝ<'_ (x y : ℝ) : Type₁ where
  no-eta-equality ; pattern
  constructor ℝ<'-cons
  field
    q : ℚ
    xU-q : Real.U x q
    yL-q : Real.L y q

_ℝ<_ : ℝ -> ℝ -> Type₁
x ℝ< y = ∥ x ℝ<' y ∥


abstract


  isProp-ℝ< : (x y : ℝ) -> isProp (x ℝ< y)
  isProp-ℝ< x y = squash

  irrefl-ℝ< : Irreflexive _ℝ<_
  irrefl-ℝ< {x} x<x = unsquash isPropBot (∥-map handle x<x)
    where
    handle : x ℝ<' x -> Bot
    handle (ℝ<'-cons q u  l) = Real.disjoint x q (l , u)

  ℝ-bounds->ℚ< : (x : ℝ) {q1 q2 : ℚ} -> (Real.L x q1) -> (Real.U x q2) -> q1 < q2
  ℝ-bounds->ℚ< x {q1} {q2} l u = handle (trichotomous-< q1 q2)
    where
    handle : Tri (q1 < q2) (q1 == q2) (q2 < q1) -> q1 < q2
    handle (tri< lt _ _ ) = lt
    handle (tri= _  p _ ) = bot-elim (Real.disjoint x q1 (l , (subst (Real.U x) (sym p) u)))
    handle (tri> _  _ lt) = bot-elim (Real.disjoint x q1 (l , (Real.isUpperSet-U x lt u)))

  ℝ-bounds->¬ℚ≤ : (x : ℝ) {q1 q2 : ℚ} -> (Real.L x q1) -> (Real.U x q2) -> ¬ (q2 ≤ q1)
  ℝ-bounds->¬ℚ≤ x lq1 uq2 q2≤q1 =
    irrefl-< (trans-≤-< q2≤q1 (ℝ-bounds->ℚ< x lq1 uq2))

  trans-ℝ< : Transitive _ℝ<_
  trans-ℝ< {x} {y} {z} x<y y<z = (∥-map2 handle x<y y<z)
    where
    handle : x ℝ<' y -> y ℝ<' z -> x ℝ<' z
    handle (ℝ<'-cons q1 ux-q1 ly-q1) (ℝ<'-cons q2 uy-q2 lz-q2) = (ℝ<'-cons q1 ux-q1 lz-q1)
      where
      module _ where
        q1<q2 : q1 < q2
        q1<q2 = ℝ-bounds->ℚ< y ly-q1 uy-q2
        lz-q1 : Real.L z q1
        lz-q1 = Real.isLowerSet-L z q1<q2 lz-q2

  asym-ℝ< : Asymmetric _ℝ<_
  asym-ℝ< {x} {y} x<y y<x = irrefl-ℝ< {x} (trans-ℝ< {x} {y} {x} x<y y<x)



  connected-ℝ< : (x y : ℝ) -> ¬ (x ℝ< y) -> ¬ (y ℝ< x) -> x == y
  connected-ℝ< x y x≮y y≮x = LU-paths->path x y l-path u-path
    where
    l-fun : (x y : ℝ) (q : ℚ) -> ¬ (y ℝ< x) -> Real.L x q -> Real.L y q
    l-fun x y q y≮x lx-q = unsquash (Real.isProp-L y q) (∥-map handle (Real.isUpperOpen-L x q lx-q))
      where
      handle : Σ[ r ∈ ℚ ] (q < r × (Real.L x r)) -> Real.L y q
      handle (r , (q<r , lx-r)) = unsquash (Real.isProp-L y q) (∥-map handle2 (Real.located y q r q<r))
        where
        handle2 : (Real.L y q ⊎ Real.U y r) -> Real.L y q
        handle2 (inj-l ly-q) = ly-q
        handle2 (inj-r uy-r) = bot-elim (y≮x ∣ ℝ<'-cons r uy-r lx-r ∣)

    l-path : (q : ℚ) -> Real.L x q == Real.L y q
    l-path q = (isoToPath i)
      where
      open Iso
      i : Iso (Real.L x q) (Real.L y q)
      i .fun = l-fun x y q y≮x
      i .inv = l-fun y x q x≮y
      i .rightInv _ = Real.isProp-L y q _ _
      i .leftInv _ = Real.isProp-L x q _ _

    u-fun : (x y : ℝ) (q : ℚ) -> ¬ (x ℝ< y) -> Real.U x q -> Real.U y q
    u-fun x y q x≮y ux-q = unsquash (Real.isProp-U y q) (∥-map handle (Real.isLowerOpen-U x q ux-q))
      where
      handle : Σ[ r ∈ ℚ ] (q > r × (Real.U x r)) -> Real.U y q
      handle (r , (r<q , ux-r)) = unsquash (Real.isProp-U y q) (∥-map handle2 (Real.located y r q r<q))
        where
        handle2 : (Real.L y r ⊎ Real.U y q) -> Real.U y q
        handle2 (inj-l ly-r) = bot-elim (x≮y ∣ ℝ<'-cons r ux-r ly-r ∣)
        handle2 (inj-r uy-q) = uy-q

    u-path : (q : ℚ) -> Real.U x q == Real.U y q
    u-path q = (isoToPath i)
      where
      open Iso
      i : Iso (Real.U x q) (Real.U y q)
      i .fun = u-fun x y q x≮y
      i .inv = u-fun y x q y≮x
      i .rightInv _ = Real.isProp-U y q _ _
      i .leftInv _ = Real.isProp-U x q _ _

  comparison-ℝ< : (x y z : ℝ) -> x ℝ< z -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
  comparison-ℝ< x y z x<z = ∥-bind handle x<z
    where
    handle : x ℝ<' z -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
    handle (ℝ<'-cons q ux-q lz-q) = ∥-bind handle2 (Real.isLowerOpen-U x q ux-q)
      where
      handle2 : Σ[ r ∈ ℚ ] (r < q × Real.U x r) -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
      handle2 (r , (r<q , ux-r)) = ∥-bind handle3 (Real.located y r q r<q)
        where
        handle3 : (Real.L y r ⊎ Real.U y q) -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
        handle3 (inj-l ly-r) = ∣ inj-l (∣ ℝ<'-cons r ux-r ly-r ∣) ∣
        handle3 (inj-r uy-q) = ∣ inj-r (∣ ℝ<'-cons q uy-q lz-q ∣) ∣

trans-L-ℝ< : {q : ℚ} {x y : ℝ} -> Real.L x q -> x ℝ< y -> Real.L y q
trans-L-ℝ< {q} {x} {y} q<x x<y = unsquash (Real.isProp-L y q) (∥-map handle x<y)
  where
  handle : x ℝ<' y -> Real.L y q
  handle (ℝ<'-cons r x<r r<y) = Real.isLowerSet-L y q<r r<y
    where
    q<r : q < r
    q<r = ℝ-bounds->ℚ< x q<x x<r

trans-ℝ<-U : {q : ℚ} {x y : ℝ} -> x ℝ< y -> Real.U y q -> Real.U x q
trans-ℝ<-U {q} {x} {y} x<y y<q = unsquash (Real.isProp-U x q) (∥-map handle x<y)
  where
  handle : x ℝ<' y -> Real.U x q
  handle (ℝ<'-cons r x<r r<y) = Real.isUpperSet-U x r<q x<r
    where
    r<q : r < q
    r<q = ℝ-bounds->ℚ< y r<y y<q

private
  _ℝ#_ : ℝ -> ℝ -> Type₁
  x ℝ# y = (x ℝ< y) ⊎ (y ℝ< x)

  isProp-ℝ# : (x y : ℝ) -> isProp (x ℝ# y)
  isProp-ℝ# x y = isProp⊎ (isProp-ℝ< x y) (isProp-ℝ< y x) (asym-ℝ< {x} {y})

  irrefl-ℝ# : Irreflexive _ℝ#_
  irrefl-ℝ# {x} (inj-l x<x) = irrefl-ℝ< {x} x<x
  irrefl-ℝ# {x} (inj-r x<x) = irrefl-ℝ< {x} x<x

  sym-ℝ# : Symmetric _ℝ#_
  sym-ℝ# {x} (inj-l x<y) = (inj-r x<y)
  sym-ℝ# {x} (inj-r y<x) = (inj-l y<x)

  comparison-ℝ# : Comparison _ℝ#_
  comparison-ℝ# x y z (inj-l x<z) = ∥-map handle (comparison-ℝ< x y z x<z)
    where
    handle : (x ℝ< y) ⊎ (y ℝ< z) → (x ℝ# y) ⊎ (y ℝ# z)
    handle (inj-l lt) = (inj-l (inj-l lt))
    handle (inj-r lt) = (inj-r (inj-l lt))
  comparison-ℝ# x y z (inj-r z<x) = ∥-map handle (comparison-ℝ< z y x z<x)
    where
    handle : (z ℝ< y) ⊎ (y ℝ< x) → (x ℝ# y) ⊎ (y ℝ# z)
    handle (inj-l lt) = (inj-r (inj-r lt))
    handle (inj-r lt) = (inj-l (inj-r lt))

  tight-ℝ# : Tight _ℝ#_
  tight-ℝ# {x} {y} p = connected-ℝ< x y (p ∘ inj-l) (p ∘ inj-r)

  TightApartness-ℝ# : TightApartness _ℝ#_
  TightApartness-ℝ# = tight-ℝ# , (\{x} -> irrefl-ℝ# {x}) , (\{x} {y} -> sym-ℝ# {x} {y}) , comparison-ℝ#

instance
  TightApartnessStr-ℝ : TightApartnessStr ℝ ℓ-one
  TightApartnessStr-ℝ = record
    { _#_ = _ℝ#_
    ; TightApartness-# = TightApartness-ℝ#
    ; isProp-# = isProp-ℝ#
    }
