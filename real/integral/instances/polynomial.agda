{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.instances.polynomial where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finsum.arithmetic
open import funext
open import integral-domain.instances.real
open import order
open import order.instances.real
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-integral-domain
open import ordered-ring.absolute-value
open import ordered-semiring.instances.real
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.epsilon-bounded
open import real.integral.delta-fine-partition
open import real.integral.is-integral
open import real.integral.partition
open import real.integral.partition-index
open import real.integral.tagged-partition
open import real.order
open import real.rational
open import relation
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import truncation

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)


IntegralOf-zero : IntegralOf (\_ -> 0#) (\_ _ -> 0#)
IntegralOf-zero a b = record
  { <-case = <-case
  ; >-case = >-case
  ; ε-case = ε-case
  }
  where
  f : ℝ -> ℝ
  f _ = 0#

  -- TODO change finiteMerge-ε
  zero-sum : {a b : ℝ} -> (tp : TaggedPartition a b) -> riemann-sum f tp == 0#
  zero-sum (p , t) = finiteMerge-ε _ elem-path
    where
    module p = Partition p
    module t = Tagging t
    elem-path : ∀ i -> f (t.t i) * p.width i == 0#
    elem-path _ = *-left-zero


  <-case : a < b -> isOrderedIntegral' a b f 0#
  <-case a<b = record
    { a<b = a<b
    ; δε = δε
    }
    where
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) 0#))
    -- TODO Move 0<1 to general location
    δε ε⁺@(ε , 0<ε) = ∣ (1# , 0<1) , εB ∣
      where
      εB : (p : TaggedPartition a b) -> isδFine 1# ⟨ p ⟩ ->
           εBounded ε (diff (riemann-sum f p) 0#)
      εB tp@(p , t) _ = subst (εBounded ε) full-path (εBounded-zero ε⁺)
        where
        full-path : 0# == diff (riemann-sum f tp) 0#
        full-path = sym minus-zero >=>
                    cong -_ (sym (zero-sum tp)) >=>
                    sym +-left-zero

  >-case : b < a -> isOrderedIntegral' b a f (- 0#)
  >-case b<a = record
    { a<b = b<a
    ; δε = δε
    }
    where
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition b a) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) (- 0#)))
    δε ε⁺@(ε , 0<ε) = ∣ (1# , 0<1) , εB ∣
      where
      εB : (p : TaggedPartition b a) -> isδFine 1# ⟨ p ⟩ ->
           εBounded ε (diff (riemann-sum f p) (- 0#))
      εB tp@(p , t) _ = subst (εBounded ε) full-path (εBounded-zero ε⁺)
        where
        full-path : 0# == diff (riemann-sum f tp) (- 0#)
        full-path = sym minus-zero >=>
                    cong -_ (sym (zero-sum tp)) >=>
                    sym +-left-zero >=>
                    +-left (sym minus-zero)

  ε-case : ∃[ k ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) -> εBounded (⟨ k ⟩ * ⟨ ε ⟩) 0#)
  ε-case = ∣ (1# , 0<1) , (\{ (_ , 0<ε) _ -> εBounded-zero (_ , trans-<-= 0<ε (sym *-left-one)) }) ∣

IntegralOf-constant : (k : ℝ) -> IntegralOf (\_ -> k) (\a b -> k * (diff a b))
IntegralOf-constant k a b = record
  { <-case = <-case
  ; >-case = >-case
  ; ε-case = ε-case
  }
  where
  f : ℝ -> ℝ
  f _ = k

  constant-sum : {a b : ℝ} -> (tp : TaggedPartition a b) -> riemann-sum f tp == k * (diff a b)
  constant-sum (p , t) =
    finiteSum-* >=> *-right (sum-width p)
    where
    module p = Partition p
    module t = Tagging t


  <-case : a < b -> isOrderedIntegral' a b f (k * (diff a b))
  <-case a<b = record
    { a<b = a<b
    ; δε = δε
    }
    where
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) (k * (diff a b))))
    δε ε⁺@(ε , 0<ε) = ∣ (1# , 0<1) , εB ∣
      where
      εB : (p : TaggedPartition a b) -> isδFine 1# ⟨ p ⟩ ->
           εBounded ε (diff (riemann-sum f p) (k * (diff a b)))
      εB tp@(p , t) _ = subst (εBounded ε) full-path (εBounded-zero ε⁺)
        where
        full-path : 0# == diff (riemann-sum f tp) (k * (diff a b))
        full-path = sym +-inverse >=> +-left (constant-sum tp)

  >-case : b < a -> isOrderedIntegral' b a f (- (k * (diff a b)))
  >-case b<a = record
    { a<b = b<a
    ; δε = δε
    }
    where
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition b a) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) (- (k * (diff a b)))))
    δε ε⁺@(ε , 0<ε) = ∣ (1# , 0<1) , εB ∣
      where
      εB : (p : TaggedPartition b a) -> isδFine 1# ⟨ p ⟩ ->
           εBounded ε (diff (riemann-sum f p) (- (k * (diff a b))))
      εB tp@(p , t) _ = subst (εBounded ε) full-path (εBounded-zero ε⁺)
        where
        full-path : 0# == diff (riemann-sum f tp) (- (k * (diff a b)))
        full-path =
          sym +-inverse >=>
          cong2 diff (sym (constant-sum tp)) (*-right diff-anticommute >=> minus-extract-right)


  ε-case : ∃[ k2 ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) ->
                         εBounded (⟨ k2 ⟩ * ⟨ ε ⟩) (k * (diff a b)))
  ε-case = ∥-bind handle (trichotomous-εBounded (1# , 0<1) k)
    where
    Ans = Σ[ k2 ∈ ℚ⁺ ] (∀ (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff a b) ->
                        εBounded (⟨ k2 ⟩ * ⟨ ε ⟩) (k * (diff a b)))
    handle : Tri⊎ (k < 0#) (εBounded 1# k) (0# < k) -> ∥ Ans ∥
    handle (tri⊎-< k<0) = ∥-map handle2 (Real.Inhabited-L k)
      where
      handle2 : Σ[ k' ∈ ℚ ] (Real.L k k') -> Ans
      handle2 (k' , Lk') = (- k' , 0<-k') , \ (ε , _) εB -> εBounded-* _ _ kB εB
        where
        k'<0 = (L->ℚ< (trans-L-ℝ< Lk' k<0))
        0<-k' = minus-flips-<0 k'<0

        kB : εBounded (- k') k
        kB = subst (Real.L k) (sym minus-double-inverse) Lk' ,
             Real.isUpperSet-U k 0<-k' (ℝ<->U k<0)
    handle (tri⊎-> 0<k) = ∥-map handle2 (Real.Inhabited-U k)
      where
      handle2 : Σ[ k' ∈ ℚ ] (Real.U k k') -> Ans
      handle2 (k' , Uk') = (k' , 0<k') , \ (ε , _) εB -> εBounded-* _ _ kB εB
        where
        0<k' = U->ℚ< (trans-ℝ<-U 0<k Uk')
        -k'<0 = minus-flips-0< 0<k'

        kB : εBounded k' k
        kB = Real.isLowerSet-L k -k'<0 (ℝ<->L 0<k) , Uk'
    handle (tri⊎-= kB) = ∣ ((1# , 0<1) , \ (ε , _) εB -> εBounded-* _ _ kB εB) ∣
