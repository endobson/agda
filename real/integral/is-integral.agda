{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.is-integral where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import funext
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.integral.harmonic-partition
open import real.integral.partition
open import real.integral.tagged-partition
open import real.interval
open import real.minimum
open import real.rational
open import real.sequence.cauchy
open import real.sequence.limit-point
open import relation
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sigma.base
open import truncation

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

record isOrderedIntegral' (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  no-eta-equality
  field
    a≤b : a ≤ b
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) v))

data isIntegral' (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  isIntegral'-≤-cons : a ≤ b -> isOrderedIntegral' a b f v -> isIntegral' a b f v
  isIntegral'-≥-cons : a ≥ b -> isOrderedIntegral' b a f (- v) -> isIntegral' a b f v

isIntegral : (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) -> Type₁
isIntegral a b f v = ∥ isIntegral' a b f v ∥

private
  isProp-isOrderedIntegral' : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isOrderedIntegral' a b f v)
  isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.a≤b =
    isProp-≤ (isOrderedIntegral'.a≤b i1) (isOrderedIntegral'.a≤b i2) i
  isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.δε ε =
    squash (isOrderedIntegral'.δε i1 ε) (isOrderedIntegral'.δε i2 ε) i


  εBounded->zero-path : (x : ℝ) -> ((ε : ℚ⁺) -> εBounded ⟨ ε ⟩ x) -> x == 0#
  εBounded->zero-path x εB = sym (ℝ∈Iℚ->path 0# x f)
    where
    f : (qi : Iℚ) -> ℝ∈Iℚ 0# qi -> ℝ∈Iℚ x qi
    f qi@(Iℚ-cons l u _) (0L-l , 0U-u) = handle (split-< u (- l))
      where
      l<0 = L->ℚ< 0L-l
      0<u = U->ℚ< 0U-u
      0<-l = minus-flips-<0 l<0
      handle : (u < (- l)) ⊎ ((- l) ≤ u) -> ℝ∈Iℚ x qi
      handle (inj-l u<-l) = Real.isLowerSet-L x _ _ l<-u (proj₁ x∈u) , proj₂ x∈u
        where
        l<-u = trans-=-< (sym minus-double-inverse) (minus-flips-< u<-l)
        x∈u = εB (u , 0<u)
      handle (inj-r -l≤u) = subst (Real.L x) minus-double-inverse (proj₁ x∈-l) ,
                            isUpperSet≤ x _ _ -l≤u (proj₂ x∈-l)
        where
        x∈-l = εB (- l , 0<-l)

  εBounded-diff->path : (x y : ℝ) -> ((ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff x y)) -> x == y
  εBounded-diff->path x y εB =
    sym (sym diff-step >=> cong (x +_) (εBounded->zero-path (diff x y) εB) >=> +-right-zero)


  isProp-ΣisOrderedIntegral' : {a b : ℝ} {f : ℝ -> ℝ} -> isProp (Σ ℝ (isOrderedIntegral' a b f))
  isProp-ΣisOrderedIntegral' {a} {b} {f} (v1 , i1) (v2 , i2) =
    ΣProp-path isProp-isOrderedIntegral' (εBounded-diff->path v1 v2 g)
    where
    a≤b = isOrderedIntegral'.a≤b i1

    g : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff v1 v2)
    g (ε , 0<ε) =
      unsquash (isProp-εBounded ε (diff v1 v2))
        (∥-bind2 handle (isOrderedIntegral'.δε i1 (ε/2 , 0<ε/2))
                        (isOrderedIntegral'.δε i2 (ε/2 , 0<ε/2)))
      where
      ε/2 = 1/2r * ε
      0<ε/2 = *-preserves-0< Pos-1/2r 0<ε

      handle : Σ[ δ ∈ ℝ⁺ ] (
                 (p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
                 εBounded ε/2 (diff (riemann-sum f p) v1)) ->
               Σ[ δ ∈ ℝ⁺ ] (
                 (p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
                 εBounded ε/2 (diff (riemann-sum f p) v2)) ->
               ∥ εBounded ε (diff v1 v2) ∥
      handle ((δ1 , 0<δ1) , tp1-f) ((δ2 , 0<δ2) , tp2-f) =
        ∥-map handle2 (∃δFinePartition a≤b (δ , 0<δ))
        where
        δ = minℝ δ1 δ2
        0<δ = minℝ-<-both 0<δ1 0<δ2

        handle2 : Σ (Partition a b) (isδFine δ) -> εBounded ε (diff v1 v2)
        handle2 (p , δ-p) = εB
          where
          t = left-tagging p
          εB1 = tp1-f (p , t) (weaken-isδFine (minℝ-≤-left δ1 δ2) p δ-p)
          εB2 = tp2-f (p , t) (weaken-isδFine (minℝ-≤-right δ1 δ2) p δ-p)
          εB1' = subst (εBounded ε/2) (sym diff-anticommute)
                   (εBounded-- (diff (riemann-sum f (p , t)) v1) εB1)
          εB = subst2 εBounded (1/2r-path' ε) diff-trans
                 (εBounded-+ (diff v1 (riemann-sum f (p , t)))
                             (diff (riemann-sum f (p , t)) v2) εB1' εB2)




isProp-isIntegral : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isIntegral a b f v)
isProp-isIntegral = squash

private
  module _ {a b : ℝ} (a=b : a == b) (p : Partition a b) where
    n = Partition.n p
    u = Partition.u p
    width = Partition.width p

    trivial-interval->ui=a : (i : Fin (suc n)) -> (u i) == a
    trivial-interval->ui=a i =
      antisym-≤ (trans-≤-= (Partition.ui≤b p i) (sym a=b)) (Partition.a≤ui p i)

    trivial-interval->zero-width : (i : Fin n) -> (width i) == 0#
    trivial-interval->zero-width i =
      cong2 diff (trivial-interval->ui=a (inc-fin i)) (trivial-interval->ui=a (suc-fin i)) >=>
      +-inverse

    trivial-interval->zero-sum : (t : Tagging p) -> (f : ℝ -> ℝ) -> riemann-sum f (p , t) == 0#
    trivial-interval->zero-sum t f =
      cong finiteSum f-p >=> finiteMerge-ε _
      where
      f-p : (\ (i : Fin n) -> (Tagging.t t i * width i) ) == (\i -> 0#)
      f-p = funExt (\i -> *-right (trivial-interval->zero-width i) >=> *-right-zero)

  module _ {a b : ℝ} {v : ℝ} {f : ℝ -> ℝ} where
    trivial-interval->zero-ordered-integral : a == b -> isOrderedIntegral' a b f v -> v == 0#
    trivial-interval->zero-ordered-integral a=b i =
      εBounded->zero-path v bound
      where
      bound : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ v
      bound ε = unsquash (isProp-εBounded ⟨ ε ⟩ v) (∥-bind handle (isOrderedIntegral'.δε i ε))
        where
        handle : Σ[ δ ∈ ℝ⁺ ] ((p : TaggedPartition a b) -> isδFine ⟨ δ ⟩ ⟨ p ⟩ ->
                              εBounded ⟨ ε ⟩ (diff (riemann-sum f p) v)) ->
                 ∥ εBounded ⟨ ε ⟩ v ∥
        handle (δ , p-bound) = ∥-map handle2 (∃δFinePartition (path-≤ a=b) δ)
          where
          handle2 : Σ (Partition a b) (isδFine ⟨ δ ⟩) -> εBounded ⟨ ε ⟩ v
          handle2 (p , δp) =
            subst (εBounded ⟨ ε ⟩) diff-path (p-bound tp δp)
            where
            tp = (p , left-tagging p)
            diff-path : (diff (riemann-sum f tp) v) == v
            diff-path =
              (cong2 diff (trivial-interval->zero-sum a=b p (left-tagging p) f) refl) >=>
              +-right minus-zero >=>
              +-right-zero

isProp-ΣisIntegral : {a b : ℝ} {f : ℝ -> ℝ} -> isProp (Σ ℝ (isIntegral a b f))
isProp-ΣisIntegral {a} {b} {f} (v1 , i1) (v2 , i2) =
  ΣProp-path isProp-isIntegral (unsquash (isSet-ℝ v1 v2) (∥-map2 handle i1 i2))
  where
  handle : isIntegral' a b f v1 -> isIntegral' a b f v2 -> v1 == v2
  handle (isIntegral'-≤-cons _ oi1) (isIntegral'-≤-cons _ oi2) =
    cong fst (isProp-ΣisOrderedIntegral' (v1 , oi1) (v2 , oi2))
  handle (isIntegral'-≥-cons _ oi1) (isIntegral'-≥-cons _ oi2) =
    sym minus-double-inverse >=>
    cong -_ (cong fst (isProp-ΣisOrderedIntegral' (- v1 , oi1) (- v2 , oi2))) >=>
    minus-double-inverse
  handle (isIntegral'-≤-cons a≤b oi1) (isIntegral'-≥-cons b≤a oi2) =
    trivial-interval->zero-ordered-integral a=b oi1 >=>
    sym minus-zero >=>
    cong -_ (sym (trivial-interval->zero-ordered-integral (sym a=b) oi2)) >=>
    minus-double-inverse
    where
    a=b = antisym-≤ a≤b b≤a
  handle (isIntegral'-≥-cons b≤a oi1) (isIntegral'-≤-cons a≤b oi2) =
    sym (trivial-interval->zero-ordered-integral a=b oi2 >=>
         sym minus-zero >=>
         cong -_ (sym (trivial-interval->zero-ordered-integral (sym a=b) oi1)) >=>
         minus-double-inverse)
    where
    a=b = antisym-≤ a≤b b≤a
