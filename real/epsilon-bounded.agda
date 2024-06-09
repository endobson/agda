{-# OPTIONS --cubical --safe --exact-split #-}

module real.epsilon-bounded where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.open-interval
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.arithmetic.rational
open import real.open-interval
open import real.order
open import real.rational
open import real.sequence
open import relation
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import truncation
open import univalence

open import real.epsilon-bounded.base public

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

abstract
  εBounded-+ : {ε1 ε2 : ℚ} (x y : ℝ) -> εBounded ε1 x -> εBounded ε2 y -> εBounded (ε1 + ε2) (x + y)
  εBounded-+ {ε1} {ε2} x y ε1-x ε2-y =
    subst (Real.L (x + y)) (sym minus-distrib-plus) (proj₁ both) ,
    proj₂ both
    where
    module _ where
      both = ℝ∈Iℚ-+ x y (curry (ℝ-bounds->Iℚ x) ε1-x) (curry (ℝ-bounds->Iℚ y) ε2-y) ε1-x ε2-y

  εBounded-- : {ε : ℚ} (x : ℝ) -> εBounded ε x -> εBounded ε (- x)
  εBounded-- {ε} x ε-x = l , subst (Real.U (- x)) minus-double-inverse u
    where
    b : ℝ∈Iℚ (- x) (i- (curry (ℝ-bounds->Iℚ x) ε-x))
    b = ℝ∈Iℚ-- x (curry (ℝ-bounds->Iℚ x) ε-x) ε-x
    l : Real.L (- x) (- ε)
    l = proj₁ b
    u : Real.U (- x) (- (- ε))
    u = proj₂ b

  εBounded-minus-eq : {ε : ℚ} (x : ℝ) -> εBounded ε x ≃ εBounded ε (- x)
  εBounded-minus-eq {ε} x =
    isoToEquiv (isProp->iso (εBounded-- x) f (isProp-εBounded ε x) (isProp-εBounded ε (- x)))
    where
    f : εBounded ε (- x) -> εBounded ε x
    f εB = subst (εBounded ε) minus-double-inverse (εBounded-- (- x) εB)

  εBounded-diff : {ε1 ε2 : ℚ} {a b : ℝ} -> εBounded ε1 a -> εBounded ε2 b ->
                  εBounded (ε1 + ε2) (diff a b)
  εBounded-diff {ε1} {ε2} {a} {b} εBa εBb =
    subst (\ε -> εBounded ε (diff a b)) +-commute (εBounded-+ _ _ εBb (εBounded-- _ εBa))

  εBounded-* : {ε1 ε2 : ℚ} (x y : ℝ) -> εBounded ε1 x -> εBounded ε2 y -> εBounded (ε1 * ε2) (x * y)
  εBounded-* {ε1} {ε2} x y ε1-x ε2-y =
    subst (ℝ∈Iℚ (x * y)) (sym (i*-SymI-path iε1 iε2 refl refl)) ℝ∈Iℚ-xy
    where
    iε1 : Iℚ
    iε1 = εBounded->Iℚ x ε1-x
    iε2 : Iℚ
    iε2 = εBounded->Iℚ y ε2-y
    ℝ∈Iℚ-xy : ℝ∈Iℚ (x * y) (iε1 i* iε2)
    ℝ∈Iℚ-xy = ℝ∈Iℚ-* x y iε1 iε2 (εBounded->ℝ∈Iℚ x ε1-x) (εBounded->ℝ∈Iℚ y ε2-y)

  εBounded-abs<ε : {ε : ℚ} {x : ℝ} -> abs x < ℚ->ℝ ε -> εBounded ε x
  εBounded-abs<ε {ε} {x} ax<ε = ℝ<->L -ε<x , ℝ<->U x<ε
    where
    x<ε : x < ℚ->ℝ ε
    x<ε = trans-≤-< max-≤-left ax<ε
    -x<ε : (- x) < ℚ->ℝ ε
    -x<ε = trans-≤-< max-≤-right ax<ε

    -ε<x : (ℚ->ℝ (- ε)) < x
    -ε<x = trans-=-< ℚ->ℝ-preserves-- (trans-<-= (minus-flips-< -x<ε) minus-double-inverse)

  εBounded-abs≤ : {ε : ℚ} {x y : ℝ} -> abs x ≤ y -> εBounded ε y -> εBounded ε x
  εBounded-abs≤ {ε} {x} {y} ax≤y εy = εBounded-abs<ε ax<ε
    where
    y<ε : y < ℚ->ℝ ε
    y<ε = U->ℝ< (proj₂ εy)
    ax<ε : abs x < ℚ->ℝ ε
    ax<ε = trans-≤-< ax≤y y<ε

  ¬εBounded-< : {a b : ℝ} -> a < b -> ∃[ ε ∈ ℚ⁺ ] ¬ (εBounded ⟨ ε ⟩ (diff a b))
  ¬εBounded-< {a} {b} a<b = ∥-map handle 0<ab
    where
    module _ where
      ab = diff a b
      0<ab = diff-0<⁺ a<b
      handle : 0# ℝ<' (diff a b) -> Σ[ ε ∈ ℚ⁺ ] ¬ (εBounded ⟨ ε ⟩ (diff a b))
      handle (ℝ<'-cons q 0U-q abL-q) =
        (q , U->ℚ< 0U-q) , (\{ (_ , abU-q) -> Real.disjoint ab q (abL-q , abU-q) })


  ¬εBounded-# : {a b : ℝ} -> a # b -> ∃[ ε ∈ ℚ⁺ ] ¬ (εBounded ⟨ ε ⟩ (diff a b))
  ¬εBounded-# (inj-l a<b) = ¬εBounded-< a<b
  ¬εBounded-# {a} {b} (inj-r b<a) = subst (\εB -> ∃[ ε ∈ ℚ⁺ ] ¬ (εB ε)) (funExt path) ¬εB
    where
    module _ where
      ¬εB = ¬εBounded-< b<a
      path : (ε : ℚ⁺) -> (εBounded ⟨ ε ⟩ (diff b a)) == (εBounded ⟨ ε ⟩ (diff a b))
      path ε = (ua (εBounded-minus-eq (diff b a))) >=>
               cong (εBounded ⟨ ε ⟩) (sym diff-anticommute)

  ℝ∈Iℚ->εBounded-diff : (i : Iℚ) (x y : ℝ) -> (ℝ∈Iℚ x i) -> (ℝ∈Iℚ y i) -> εBounded (i-width i) (diff x y)
  ℝ∈Iℚ->εBounded-diff i@(Iℚ-cons l u _) x y (Lx , Ux) (Ly , Uy) = Ld , Ud
    where
    w : ℚ
    w = diff l u
    Ld : Real.L (diff x y) (- w)
    Ld = ℝ<->L
          (trans-=-< ℚ->ℝ-preserves--
            (trans-<-= (minus-flips-< (trans-<-= (+-preserves-< (U->ℝ< Ux) (minus-flips-< (L->ℝ< Ly)))
                                                 (sym ℚ->ℝ-preserves-diff)))
               (sym diff-anticommute)))
    Ud : Real.U (diff x y) w
    Ud = ℝ<->U
          (trans-<-= (+-preserves-< (U->ℝ< Uy) (minus-flips-< (L->ℝ< Lx)))
                                               (sym ℚ->ℝ-preserves-diff))
