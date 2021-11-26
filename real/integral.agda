{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral where

open import abs
open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import fin
open import finset.instances
open import finsum
open import hlevel
open import nat.properties
open import order
open import order.instances.nat
open import order.instances.real
open import integral-domain.instances.real
open import ordered-integral-domain
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.heyting-field
open import real.arithmetic.rational
open import real.arithmetic.multiplication.inverse
open import real.interval
open import real.minimum
open import real.order
open import real.rational
open import real.sequence.cauchy
open import real.sequence.limit-point
open import ring
open import ring.implementations
open import ring.implementations.real
open import semiring
open import sigma.base
open import truncation

import int

record TaggedPartition (a : ℝ) (b : ℝ) : Type₁ where
  no-eta-equality
  field
    n : ℕ
    u : Fin (suc n) -> ℝ
    u0=a : u zero-fin == a
    un=b : u (n , refl-≤) == b
    t : Fin n -> ℝ
    t<u : (i : Fin n) -> t i < u (suc-fin i)
    u<t : (i : Fin n) -> u (inc-fin i) < t i

  width : (i : Fin n) -> ℝ
  width i = (diff (u (inc-fin i)) (u (suc-fin i)))

riemann-sum : {a b : ℝ} -> (f : ℝ -> ℝ) -> TaggedPartition a b -> ℝ
riemann-sum f p = 
  finiteSum (\ (i : Fin p.n) -> p.t i * p.width i)
  where
  module p = TaggedPartition p

isδFinePartition : {a b : ℝ} (δ : ℝ) (p : TaggedPartition a b) -> Type₁
isδFinePartition δ p = (i : Fin p.n) -> p.width i ≤ δ
  where
  module p = TaggedPartition p

weaken-isδFinePartition : {a b : ℝ} {δ1 δ2 : ℝ} -> δ1 ≤ δ2 -> (p : TaggedPartition a b) -> 
                          isδFinePartition δ1 p -> isδFinePartition δ2 p
weaken-isδFinePartition δ1≤δ2 _ f i = trans-≤ (f i) δ1≤δ2


ℕ->TaggedPartition : (a b : ℝ) -> (a < b) -> (n : ℕ) -> TaggedPartition a b
ℕ->TaggedPartition a b a<b n .TaggedPartition.n = suc n
ℕ->TaggedPartition a b a<b n .TaggedPartition.u (i , _) = 
  (ℚ->ℝ (ℕ->ℚ i)) * (ℚ->ℝ (1/ℕ (suc n , tt))) * (diff a b) + a
ℕ->TaggedPartition a b a<b n .TaggedPartition.u0=a =
  +-left (*-left *-left-zero >=> *-left-zero) >=> +-left-zero
ℕ->TaggedPartition a b a<b n .TaggedPartition.un=b =
  +-left (*-left (sym ℚ->ℝ-preserves-* >=> 
                  cong ℚ->ℝ (*-commute >=> (1/ℕ-ℕ-path (suc n , _)))) >=> 
          *-left-one) >=>
  +-commute >=> 
  diff-step
ℕ->TaggedPartition a b a<b n .TaggedPartition.t (i , _) = 
  (ℚ->ℝ (1/2r + (ℕ->ℚ i))) * (ℚ->ℝ (1/ℕ (suc n , tt))) * (diff a b) + a

ℕ->TaggedPartition a b a<b n .TaggedPartition.t<u (i , _) = 
  +₂-preserves-< 
    (*₂-preserves-< (*₂-preserves-<
                      (ℚ->ℝ-preserves-< _ _ 1/2+i<suc-i)
                      (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))) 0<d)
  where
  0<d : 0# ℝ< (diff a b)
  0<d = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)
  1/2+i<suc-i : (1/2r + (ℕ->ℚ i)) < (ℕ->ℚ (suc i))
  1/2+i<suc-i = trans-<-= (+₂-preserves-< 1/2r<1r) (sym si=1+i)
    where
    si=1+i : ℤ->ℚ (int.int (suc i)) == 1r + ℤ->ℚ (int.int i)
    si=1+i = 
      cong ℤ->ℚ (int-inject-+') >=> 
      ℤ->ℚ-preserves-+ 1# (int.int i)
ℕ->TaggedPartition a b a<b n .TaggedPartition.u<t (i , _) = 
  +₂-preserves-< 
    (*₂-preserves-< (*₂-preserves-<
                      (ℚ->ℝ-preserves-< _ _ i<1/2+i)
                      (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))) 0<d)
  where
  0<d : 0# ℝ< (diff a b)
  0<d = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)
  i<1/2+i : ℕ->ℚ i < (1/2r + (ℕ->ℚ i))
  i<1/2+i = trans-=-< (sym +-left-zero) (+₂-preserves-< Pos-1/2r)


isδFinePartition-ℕ->TaggedPartition : 
  (a b : ℝ) -> (a<b : a < b) -> (n : ℕ) -> 
  isδFinePartition (ℚ->ℝ (1/ℕ (suc n , tt)) * diff a b) (ℕ->TaggedPartition a b a<b n)
isδFinePartition-ℕ->TaggedPartition a b a<b n i = path-≤ tp-width-path
  where
  1/sn = (ℚ->ℝ (1/ℕ (suc n , tt)))
  tp = (ℕ->TaggedPartition a b a<b n)
  module tp = TaggedPartition tp
    
  i-path : diff (ℚ->ℝ (ℕ->ℚ (Fin.i (inc-fin i))))
                (ℚ->ℝ (ℕ->ℚ (Fin.i (suc-fin i)))) == 1#
  i-path = 
    sym ℚ->ℝ-preserves-diff >=>
    cong ℚ->ℝ (sym (ℤ->ℚ-preserves-diff _ _) >=>
               cong ℤ->ℚ (int.add1-extract-left >=> cong int.add1 +-inverse))
   

  tp-width-path : tp.width i == 1/sn * diff a b
  tp-width-path = 
    sym +-swap-diff >=>
    +-right +-inverse >=>
    +-right-zero >=>
    sym *-distrib-diff-right >=>
    *-left (sym *-distrib-diff-right >=>
            *-left i-path >=>
            *-left-one)



ℝ⁺ : Type₁
ℝ⁺ = Σ ℝ (0# <_)

record isIntegral (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  no-eta-equality
  field
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFinePartition ⟨ δ ⟩ p ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) v))

isProp-isIntegral : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isIntegral a b f v)
isProp-isIntegral i1 i2 i .isIntegral.δε ε =
  squash (isIntegral.δε i1 ε) (isIntegral.δε i2 ε) i


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

small-1/ℕ-ℝ : (x : ℝ⁺) -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < ⟨ x ⟩)
small-1/ℕ-ℝ (x , 0<x) = ∥-bind handle 0<x
  where
  handle : 0# ℝ<' x -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
  handle (ℝ<'-cons q 0<q q<x) = ∥-map handle2 (small-1/ℕ (q , U->ℚ< 0<q))
    where
    handle2 : Σ[ m ∈ Nat⁺ ] (1/ℕ m) < q -> 
              Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
    handle2 (m , 1/m<q) = m , ∣ (ℝ<'-cons q (ℚ<->U 1/m<q) q<x) ∣


isProp-ΣisIntegral : {a b : ℝ} {f : ℝ -> ℝ} -> a < b -> isProp (Σ ℝ (isIntegral a b f))
isProp-ΣisIntegral {a} {b} {f} a<b (v1 , i1) (v2 , i2) =
  ΣProp-path isProp-isIntegral v1=v2
  where
  g : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff v1 v2)
  g (ε , 0<ε) = 
    unsquash (isProp-εBounded ε (diff v1 v2))
      (∥-bind2 handle (isIntegral.δε i1 (ε/2 , 0<ε/2)) (isIntegral.δε i2 (ε/2 , 0<ε/2)))
    where
    ε/2 = 1/2r * ε
    0<ε/2 = *-preserves-0< Pos-1/2r 0<ε
    handle : Σ[ δ ∈ ℝ⁺ ] (
               (p : TaggedPartition a b) -> isδFinePartition ⟨ δ ⟩ p ->
               εBounded ε/2 (diff (riemann-sum f p) v1)) ->
             Σ[ δ ∈ ℝ⁺ ] (
               (p : TaggedPartition a b) -> isδFinePartition ⟨ δ ⟩ p ->
               εBounded ε/2 (diff (riemann-sum f p) v2)) ->
             ∥ εBounded ε (diff v1 v2) ∥
    handle ((δ1 , 0<δ1) , tp1-f) ((δ2 , 0<δ2) , tp2-f) = 
      ∥-map handle2 (small-1/ℕ-ℝ (δ/ab , 0<δ/ab))
      where
      ab = diff a b
      0<ab = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)
      1/ab = ℝ1/ ab (inj-r 0<ab)
      0<1/ab : 0# < 1/ab
      0<1/ab =
        *₂-reflects-<
          (subst2 _<_ (sym *-left-zero) (sym (ℝ1/-inverse ab (inj-r 0<ab))) 0<1)
          0<ab
      δ = minℝ δ1 δ2
      0<δ = minℝ-<-both 0<δ1 0<δ2
      δ/ab = δ * 1/ab
      0<δ/ab = *-preserves-0< 0<δ 0<1/ab

      handle2 : Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < δ/ab) -> 
                εBounded ε (diff v1 v2)
      handle2 ((suc n , _) , 1/sn<δ/ab) = εB
        where
        1/sn = ℚ->ℝ (1/ℕ (suc n , tt))

        tp = ℕ->TaggedPartition a b a<b n
        δ-tp : isδFinePartition (ℚ->ℝ (1/ℕ (suc n , tt)) * diff a b) tp
        δ-tp = isδFinePartition-ℕ->TaggedPartition a b a<b n
        δ-small : (ℚ->ℝ (1/ℕ (suc n , tt)) * diff a b) < δ
        δ-small = 
          trans-<-= (*₂-preserves-< 1/sn<δ/ab 0<ab) 
                    (*-assoc >=> *-right (ℝ1/-inverse ab (inj-r 0<ab)) >=> *-right-one)

        εB1 = tp1-f tp (weaken-isδFinePartition 
                         (weaken-< (trans-<-≤ δ-small (minℝ-≤-left δ1 δ2))) tp δ-tp)
        εB2 = tp2-f tp (weaken-isδFinePartition 
                         (weaken-< (trans-<-≤ δ-small (minℝ-≤-right δ1 δ2))) tp δ-tp)
        εB1' = subst (εBounded ε/2) (sym diff-anticommute) 
                 (εBounded-- (diff (riemann-sum f tp) v1) εB1)
        εB = subst2 εBounded (1/2r-path' ε) diff-trans
               (εBounded-+ (diff v1 (riemann-sum f tp)) 
                           (diff (riemann-sum f tp) v2) εB1' εB2)


  v1=v2 : v1 == v2
  v1=v2 = εBounded-diff->path v1 v2 g
