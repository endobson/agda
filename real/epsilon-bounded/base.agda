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
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.minmax
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import rational.open-interval
open import real
open import real.arithmetic.rational
open import real.open-interval
open import real.order
open import real.rational
open import relation
open import sum
open import truncation

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
    backward (-ε<x , x<ε) = ℝ<->L (subst (_< x) (sym ℚ->ℝ-preserves--) -ε<x) , (ℝ<->U x<ε)

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

  ∃εBounded : (x : ℝ) -> ∃[ ε ∈ ℚ⁺ ] (εBounded ⟨ ε ⟩ x)
  ∃εBounded x = ∥-map2 handle (Real.Inhabited-L x) (Real.Inhabited-U x)
    where
    handle : Σ ℚ (Real.L x) -> Σ ℚ (Real.U x) -> Σ[ ε ∈ ℚ⁺ ] (εBounded ⟨ ε ⟩ x)
    handle (l , L) (u , U) =
      (max (- l) u , 0<ε) ,
      (isLowerSet≤ x (trans-=-≤ minus-max-path (trans-≤-= min-≤-left minus-double-inverse)) L ,
       isUpperSet≤ x max-≤-right U)
      where
      l<u : l < u
      l<u = ℝ-bounds->ℚ< x L U
      0<ε : 0# < max (- l) u
      0<ε = unsquash isProp-< (∥-map handle2 (comparison-< _ _ _ l<u))
        where
        handle2 : (l < 0#) ⊎ (0# < u) -> 0# < max (- l) u
        handle2 (inj-l l<0) = trans-<-≤ (minus-flips-<0 l<0) max-≤-left
        handle2 (inj-r 0<u) = trans-<-≤ 0<u max-≤-right


εBounded->0<ε : {ε : ℚ} (x : ℝ) -> εBounded ε x -> 0# < ε
εBounded->0<ε {ε} x (-ε<x , x<ε) = proj-¬r (split-< 0# ε) ¬ε≤0
  where
  -ε<ε : ℚ->ℝ (- ε) < ℚ->ℝ ε
  -ε<ε = trans-< (L->ℝ< {x = x} -ε<x) (U->ℝ< x<ε)
  ¬ε≤0 : ¬ (ε ≤ 0#)
  ¬ε≤0 ε≤0 = irrefl-< (trans-<-≤ -ε<ε (ℚ->ℝ-preserves-≤ (trans-≤ ε≤0 (minus-flips-≤0 ε≤0))))


εBounded->Iℚ : {ε : ℚ} (x : ℝ) -> εBounded ε x -> Iℚ
εBounded->Iℚ {ε} x εB = Iℚ-cons (- ε) ε (trans-< (minus-flips-0< 0<ε) 0<ε)
  where
  0<ε : 0# < ε
  0<ε = (εBounded->0<ε x εB)

εBounded->ℝ∈Iℚ : {ε : ℚ} (x : ℝ) -> (εB : εBounded ε x) -> ℝ∈Iℚ x (εBounded->Iℚ x εB)
εBounded->ℝ∈Iℚ x εB = εB
