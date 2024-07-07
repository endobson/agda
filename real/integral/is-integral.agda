{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.is-integral where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import funext
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-field
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.epsilon-bounded
open import real.integral.delta-fine-partition
open import real.integral.partition
open import real.integral.tagged-partition
open import real.interval
open import real.rational
open import real.sequence.limit-point
open import real.subspace
open import relation
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sigma.base
open import subset.subspace
open import truncation

record isOrderedIntegral' (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  no-eta-equality
  field
    a<b : a < b
    δε : (ε : ℚ⁺) -> ∃[ (δ , _) ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFine δ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) v))

record isIntegral (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  field
    <-case : a < b -> isOrderedIntegral' a b f v
    >-case : a > b -> isOrderedIntegral' b a f (- v)
    ε-case : ∃[ k ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) -> εBounded (⟨ k ⟩ * ⟨ ε ⟩) v)

private
  isProp-isOrderedIntegral' : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isOrderedIntegral' a b f v)
  isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.a<b =
    isProp-< (isOrderedIntegral'.a<b i1) (isOrderedIntegral'.a<b i2) i
  isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.δε ε =
    squash (isOrderedIntegral'.δε i1 ε) (isOrderedIntegral'.δε i2 ε) i

  isProp-ΣisOrderedIntegral' : {a b : ℝ} {f : ℝ -> ℝ} -> isProp (Σ ℝ (isOrderedIntegral' a b f))
  isProp-ΣisOrderedIntegral' {a} {b} {f} (v1 , i1) (v2 , i2) =
    ΣProp-path isProp-isOrderedIntegral' (εBounded-diff->path v1 v2 g)
    where
    a<b = isOrderedIntegral'.a<b i1

    g : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff v1 v2)
    g (ε , 0<ε) =
      unsquash (isProp-εBounded ε (diff v1 v2))
        (∥-bind2 handle (isOrderedIntegral'.δε i1 (ε/2 , 0<ε/2))
                        (isOrderedIntegral'.δε i2 (ε/2 , 0<ε/2)))
      where
      ε/2 = 1/2 * ε
      0<ε/2 = *-preserves-0< 0<1/2 0<ε

      handle : Σ[ (δ , _) ∈ ℝ⁺ ] (
                 (p : TaggedPartition a b) -> isδFine δ ⟨ p ⟩ ->
                 εBounded ε/2 (diff (riemann-sum f p) v1)) ->
               Σ[ (δ , _) ∈ ℝ⁺ ] (
                 (p : TaggedPartition a b) -> isδFine δ ⟨ p ⟩ ->
                 εBounded ε/2 (diff (riemann-sum f p) v2)) ->
               ∥ εBounded ε (diff v1 v2) ∥
      handle ((δ1 , 0<δ1) , tp1-f) ((δ2 , 0<δ2) , tp2-f) =
        ∥-map handle2 (∃δFinePartition a<b (δ , 0<δ))
        where
        δ = min δ1 δ2
        0<δ = min-greatest-< 0<δ1 0<δ2

        handle2 : Σ (Partition a b) (isδFine δ) -> εBounded ε (diff v1 v2)
        handle2 (p , δ-p) = εB
          where
          t = left-tagging p
          εB1 = tp1-f (p , t) (weaken-isδFine min-≤-left p δ-p)
          εB2 = tp2-f (p , t) (weaken-isδFine min-≤-right p δ-p)
          εB1' = subst (εBounded ε/2) (sym diff-anticommute)
                   (εBounded-- (diff (riemann-sum f (p , t)) v1) εB1)
          εB = subst2 εBounded 1/2-path diff-trans
                 (εBounded-+ (diff v1 (riemann-sum f (p , t)))
                             (diff (riemann-sum f (p , t)) v2) εB1' εB2)


isProp-isIntegral : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isIntegral a b f v)
isProp-isIntegral i1 i2 j = record
  { <-case = isPropΠ (\_ -> isProp-isOrderedIntegral') i1.<-case i2.<-case j
  ; >-case = isPropΠ (\_ -> isProp-isOrderedIntegral') i1.>-case i2.>-case j
  ; ε-case = squash i1.ε-case i2.ε-case j
  }
  where
  module i1 = isIntegral i1
  module i2 = isIntegral i2


isProp-ΣisIntegral : {a b : ℝ} {f : ℝ -> ℝ} -> isProp (Σ ℝ (isIntegral a b f))
isProp-ΣisIntegral {a} {b} {f} (v1 , i1) (v2 , i2) =
  ΣProp-path isProp-isIntegral (tight-# ¬v1#v2)
  where
  module i1 = isIntegral i1
  module i2 = isIntegral i2
  ¬v1#v2 : ¬ (v1 # v2)
  ¬v1#v2 v1#v2 = unsquash isPropBot (∥-bind3 handle i1.ε-case i2.ε-case (¬εBounded-# v1#v2))
    where
    handle : Σ[ k1 ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) -> εBounded (⟨ k1 ⟩ * ⟨ ε ⟩) v1) ->
             Σ[ k2 ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) -> εBounded (⟨ k2 ⟩ * ⟨ ε ⟩) v2) ->
             Σ[ ε ∈ ℚ⁺ ] ¬ (εBounded ⟨ ε ⟩ (diff v1 v2)) ->
             ∥ Bot ∥
    handle ((k1 , 0<k1) , εB1) ((k2 , 0<k2) , εB2) ((ε' , 0<ε') , ¬ε'v1v2) =
      (∥-map handle2 (trichotomous-εBounded-diff (ε , 0<ε) a b))
      where
      0<k12 = +-preserves-0< 0<k1 0<k2
      k12-inv = (\ k12=0 -> irrefl-path-< (sym k12=0) 0<k12)
      ε = (r1/ (k1 + k2) k12-inv) * ε'
      0<ε = *-preserves-0< (r1/-preserves-Pos _ k12-inv 0<k12) 0<ε'
      ε⁺ : ℚ⁺
      ε⁺ = ε , 0<ε
      ε-path : (k1 * ε + k2 * ε) == ε'
      ε-path =
        sym *-distrib-+-right >=>
        sym *-assoc >=>
        *-left (*-commute >=> r1/-inverse _ k12-inv) >=>
        *-left-one


      handle2 : Tri⊎ (a < b) (εBounded ε (diff a b)) (b < a) -> Bot
      handle2 (tri⊎-< a<b) = irrefl-path-# v1=v2 v1#v2
        where
        v1=v2 : v1 == v2
        v1=v2 = cong fst (isProp-ΣisOrderedIntegral' (v1 , i1.<-case a<b) (v2 , i2.<-case a<b))
      handle2 (tri⊎-> b<a) = irrefl-path-# v1=v2 (minus-preserves-# v1#v2)
        where
        v1=v2 : (- v1) == (- v2)
        v1=v2 = cong fst (isProp-ΣisOrderedIntegral' (- v1 , i1.>-case b<a) (- v2 , i2.>-case b<a))
      handle2 (tri⊎-= εab) =
        ¬ε'v1v2 (subst (\ε -> εBounded ε (diff v1 v2)) ε-path εv1v2)
        where
        εv1 : εBounded (k1 * ε) v1
        εv1 = εB1 ε⁺ εab
        εv2 : εBounded (k2 * ε) v2
        εv2 = εB2 ε⁺ εab
        εv1v2 : εBounded (k1 * ε + k2 * ε) (diff v1 v2)
        εv1v2 = εBounded-diff εv1 εv2

IntegralOf : REL (ℝ -> ℝ) (ℝ -> ℝ -> ℝ) ℓ-one
IntegralOf f g = ∀ a b -> (isIntegral a b f (g a b))
