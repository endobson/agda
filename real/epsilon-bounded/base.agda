{-# OPTIONS --cubical --safe --exact-split #-}

module real.epsilon-bounded.base where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import hlevel
open import isomorphism
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic.rational
open import real.interval
open import real.rational
open import relation
open import truncation

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

εBounded : ℚ -> ℝ -> Type₀
εBounded ε x = Real.L x (- ε) × Real.U x ε

εBounded' : ℝ -> ℝ -> Type₁
εBounded' ε x = ((- ε) < x) × (x < ε)

abstract
  isProp-εBounded : (ε : ℚ) -> (x : ℝ) -> isProp (εBounded ε x)
  isProp-εBounded ε x = isProp× (Real.isProp-L x (- ε)) (Real.isProp-U x ε)

  isProp-εBounded' : (ε : ℝ) -> (x : ℝ) -> isProp (εBounded' ε x)
  isProp-εBounded' ε x = isProp× isProp-< isProp-<

  εBounded'-eq : ∀ ε x -> εBounded ε x ≃ εBounded' (ℚ->ℝ ε) x
  εBounded'-eq ε x =
    isoToEquiv (isProp->iso forward backward (isProp-εBounded ε x) (isProp-εBounded' (ℚ->ℝ ε) x))
    where
    forward : εBounded ε x -> εBounded' (ℚ->ℝ ε) x
    forward (l , u) = (subst (_< x) ℚ->ℝ-preserves-- (L->ℝ< l)) , (U->ℝ< u)
    backward : εBounded' (ℚ->ℝ ε) x -> εBounded ε x
    backward (-ε<x , x<ε) = ℝ<->L _ _ (subst (_< x) (sym ℚ->ℝ-preserves--) -ε<x) , (ℝ<->U _ _ x<ε)

  εBounded-zero : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ 0#
  εBounded-zero (ε , 0<ε) = (ℚ<->L (minus-flips-0< 0<ε) , ℚ<->U 0<ε)

  εBounded->zero-path : (x : ℝ) -> ((ε : ℚ⁺) -> εBounded ⟨ ε ⟩ x) -> x == 0#
  εBounded->zero-path x εB = sym (ℝ∈Iℚ->path 0# x f)
    where
    module _ where
      f : (qi : Iℚ) -> ℝ∈Iℚ 0# qi -> ℝ∈Iℚ x qi
      f qi@(Iℚ-cons l u _) (0L-l , 0U-u) = handle (split-< u (- l))
        where
        l<0 = L->ℚ< 0L-l
        0<u = U->ℚ< 0U-u
        0<-l = minus-flips-<0 l<0
        handle : (u < (- l)) ⊎ ((- l) ≤ u) -> ℝ∈Iℚ x qi
        handle (inj-l u<-l) = Real.isLowerSet-L x l<-u (proj₁ x∈u) , proj₂ x∈u
          where
          l<-u = trans-=-< (sym minus-double-inverse) (minus-flips-< u<-l)
          x∈u = εB (u , 0<u)
        handle (inj-r -l≤u) = subst (Real.L x) minus-double-inverse (proj₁ x∈-l) ,
                              isUpperSet≤ x -l≤u (proj₂ x∈-l)
          where
          x∈-l = εB (- l , 0<-l)

  εBounded-diff->path : (x y : ℝ) -> ((ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff x y)) -> x == y
  εBounded-diff->path x y εB =
    diff-zero (εBounded->zero-path (diff x y) εB)


  trichotomous-εBounded : (ε : ℚ⁺) (x : ℝ) -> ∥ Tri⊎ (x < 0#) (εBounded ⟨ ε ⟩ x) (0# < x) ∥
  trichotomous-εBounded (ε , 0<ε) x =
    ∥-map2 handle (x.located _ _ 0<ε) (x.located _ _ (minus-flips-0< 0<ε))
    where
    module x = Real x
    handle : (x.L 0# ⊎ x.U ε) -> (x.L (- ε) ⊎ x.U 0#) -> Tri⊎ (x < 0#) (εBounded ε x) (0# < x)
    handle (inj-l xL-0) _ = tri⊎-> (L->ℝ< xL-0)
    handle (inj-r xU-ε) (inj-r xU-0) = tri⊎-< (U->ℝ< xU-0)
    handle (inj-r xU-ε) (inj-l xL--ε) = tri⊎-= (xL--ε , xU-ε)


  trichotomous-εBounded-diff : (ε : ℚ⁺) (a b : ℝ) ->
    ∥ Tri⊎ (a < b) (εBounded ⟨ ε ⟩ (diff a b)) (b < a) ∥
  trichotomous-εBounded-diff ε a b = ∥-map handle (trichotomous-εBounded ε (diff a b))
    where
    handle : Tri⊎ ((diff a b) < 0#) (εBounded ⟨ ε ⟩ (diff a b)) (0# < (diff a b)) ->
             Tri⊎ (a < b)           (εBounded ⟨ ε ⟩ (diff a b)) (b < a)
    handle (tri⊎-< ab<0) = (tri⊎-> (diff-<0⁻ ab<0))
    handle (tri⊎-= ab=0) = (tri⊎-= ab=0)
    handle (tri⊎-> ab>0) = (tri⊎-< (diff-0<⁻ ab>0))

  weaken-εBounded : {ε1 ε2 : ℚ} -> ε1 ≤ ε2 -> (x : ℝ) -> εBounded ε1 x -> εBounded ε2 x
  weaken-εBounded ε1≤ε2 x (l , u) =
    isLowerSet≤ x -ε2≤-ε1 l ,
    isUpperSet≤ x ε1≤ε2 u
    where
    module _ where
      -ε2≤-ε1 = minus-flips-≤ ε1≤ε2
