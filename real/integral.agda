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
open import finite-commutative-monoid.instances
open import finsum
open import funext
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
import nat.order as no
import nat

record TaggedPartition (a : ℝ) (b : ℝ) : Type₁ where
  no-eta-equality
  field
    n : ℕ
    u : Fin (suc n) -> ℝ
    u0=a : u zero-fin == a
    un=b : u (n , refl-≤) == b
    t : Fin n -> ℝ
    t≤u : (i : Fin n) -> t i ≤ u (suc-fin i)
    u≤t : (i : Fin n) -> u (inc-fin i) ≤ t i
--    u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)

  width : (i : Fin n) -> ℝ
  width i = (diff (u (inc-fin i)) (u (suc-fin i)))

  u≤u : (i : Fin n) -> u (inc-fin i) ≤ u (suc-fin i)
  u≤u i = trans-≤ (u≤t i) (t≤u i)

riemann-sum : {a b : ℝ} -> (f : ℝ -> ℝ) -> TaggedPartition a b -> ℝ
riemann-sum f p =
  finiteSum (\ (i : Fin p.n) -> p.t i * p.width i)
  where
  module p = TaggedPartition p

-- tagged-partition->≤ : {a b : ℝ} -> TaggedPartition a b -> a ≤ b
-- tagged-partition->≤ {a} {b} tp = handle tp.n refl
--   where
--   module tp = TaggedPartition tp
--   u-preserves-<' : (i j : Fin (suc tp.n)) (k : ℕ) (p : (suc k) + (Fin.i i) == (Fin.i j)) ->
--                     tp.u i < tp.u j
--   u-preserves-<' i j zero p =
--     subst2 _<_ (cong tp.u (fin-i-path refl)) (cong tp.u (fin-i-path p)) (tp.u<u i2)
--     where
--     sn = suc tp.n
--     i' = Fin.i i
--     j' = Fin.i j
--     i<j : i' < j'
--     i<j = zero , p
--
--     j<sn : j' < sn
--     j<sn = Fin.i<n j
--
--     i<n : i' < tp.n
--     i<n = no.pred-≤ (no.trans-≤-< i<j j<sn)
--
--     i2 : Fin tp.n
--     i2 = i' , i<n
--   u-preserves-<' i j@(suc pj' , pj<sn) (suc k) p =
--     trans-< (u-preserves-<' i pj k (cong nat.pred p)) upj<uj
--     where
--     sn = suc tp.n
--     i' = Fin.i i
--     j' = Fin.i j
--
--     j<sn : j' < sn
--     j<sn = Fin.i<n j
--
--     pj : Fin sn
--     pj = inc-fin (pj' , no.pred-≤ pj<sn)
--
--     upj<uj : tp.u pj < tp.u j
--     upj<uj = subst2 _<_ (cong tp.u (fin-i-path refl)) (cong tp.u (fin-i-path refl))
--                     (tp.u<u (pj' , no.pred-≤ pj<sn))
--   u-preserves-<' i j@(zero , _) (suc k) p =
--     bot-elim (nat.zero-≮ (suc k , nat.+'-right-suc {suc k} >=> p))
--
--   u-preserves-< : (i j : Fin (suc tp.n)) -> Fin.i i < Fin.i j -> tp.u i < tp.u j
--   u-preserves-< i j (k , sk+i=j) = u-preserves-<' i j k (sym nat.+'-right-suc >=> sk+i=j)
--
--
--   handle : (n : ℕ) (path : tp.n == n) -> a ≤ b
--   handle zero       n=z  = path-≤ (sym tp.u0=a >=> cong tp.u (fin-i-path (sym n=z)) >=> tp.un=b)
--   handle (suc n') n=n' =
--     trans-=-≤ (sym tp.u0=a)
--       (trans-≤-= (weaken-< (u-preserves-< zero-fin (suc-fin (n' , path-≤ (sym n=n'))) no.zero-<))
--                  (cong tp.u (fin-i-path (sym n=n')) >=> tp.un=b))
--     where
--     check : tp.n == suc n'
--     check = n=n'

--private
--  module _ {

tagged-partition->≤ : {a b : ℝ} -> TaggedPartition a b -> a ≤ b
tagged-partition->≤ {a} {b} tp = handle tp.n refl
  where
  module tp = TaggedPartition tp
  u-preserves-≤' : (i j : Fin (suc tp.n)) (k : ℕ) (p : (suc k) + (Fin.i i) == (Fin.i j)) ->
                    tp.u i ≤ tp.u j
  u-preserves-≤' i j zero p =
    subst2 _≤_ (cong tp.u (fin-i-path refl)) (cong tp.u (fin-i-path p)) (tp.u≤u i2)
    where
    sn = suc tp.n
    i' = Fin.i i
    j' = Fin.i j
    i<j : i' < j'
    i<j = zero , p

    j<sn : j' < sn
    j<sn = Fin.i<n j

    i<n : i' < tp.n
    i<n = no.pred-≤ (no.trans-≤-< i<j j<sn)

    i2 : Fin tp.n
    i2 = i' , i<n
  u-preserves-≤' i j@(suc pj' , pj<sn) (suc k) p =
    trans-≤ (u-preserves-≤' i pj k (cong nat.pred p)) upj≤uj
    where
    sn = suc tp.n
    i' = Fin.i i
    j' = Fin.i j

    j<sn : j' < sn
    j<sn = Fin.i<n j

    pj : Fin sn
    pj = inc-fin (pj' , no.pred-≤ pj<sn)

    upj≤uj : tp.u pj ≤ tp.u j
    upj≤uj = subst2 _≤_ (cong tp.u (fin-i-path refl)) (cong tp.u (fin-i-path refl))
                    (tp.u≤u (pj' , no.pred-≤ pj<sn))
  u-preserves-≤' i j@(zero , _) (suc k) p =
    bot-elim (nat.zero-≮ (suc k , nat.+'-right-suc {suc k} >=> p))

  u-preserves-≤ : (i j : Fin (suc tp.n)) -> Fin.i i < Fin.i j -> tp.u i ≤ tp.u j
  u-preserves-≤ i j (k , sk+i=j) = u-preserves-≤' i j k (sym nat.+'-right-suc >=> sk+i=j)


  handle : (n : ℕ) (path : tp.n == n) -> a ≤ b
  handle zero       n=z  = path-≤ (sym tp.u0=a >=> cong tp.u (fin-i-path (sym n=z)) >=> tp.un=b)
  handle (suc n') n=n' =
    trans-=-≤ (sym tp.u0=a)
      (trans-≤-= (u-preserves-≤ zero-fin (suc-fin (n' , path-≤ (sym n=n'))) no.zero-<)
                 (cong tp.u (fin-i-path (sym n=n')) >=> tp.un=b))
    where
    check : tp.n == suc n'
    check = n=n'



isδFinePartition : {a b : ℝ} (δ : ℝ) (p : TaggedPartition a b) -> Type₁
isδFinePartition δ p = (i : Fin p.n) -> p.width i ≤ δ
  where
  module p = TaggedPartition p

weaken-isδFinePartition : {a b : ℝ} {δ1 δ2 : ℝ} -> δ1 ≤ δ2 -> (p : TaggedPartition a b) ->
                          isδFinePartition δ1 p -> isδFinePartition δ2 p
weaken-isδFinePartition δ1≤δ2 _ f i = trans-≤ (f i) δ1≤δ2


ℕ->TaggedPartition : (a b : ℝ) -> (a ≤ b) -> (n : ℕ) -> TaggedPartition a b
ℕ->TaggedPartition a b a≤b n .TaggedPartition.n = suc n
ℕ->TaggedPartition a b a≤b n .TaggedPartition.u (i , _) =
  (ℚ->ℝ (ℕ->ℚ i)) * (ℚ->ℝ (1/ℕ (suc n , tt))) * (diff a b) + a
ℕ->TaggedPartition a b a≤b n .TaggedPartition.u0=a =
  +-left (*-left *-left-zero >=> *-left-zero) >=> +-left-zero
ℕ->TaggedPartition a b a≤b n .TaggedPartition.un=b =
  +-left (*-left (sym ℚ->ℝ-preserves-* >=>
                  cong ℚ->ℝ (*-commute >=> (1/ℕ-ℕ-path (suc n , _)))) >=>
          *-left-one) >=>
  +-commute >=>
  diff-step
ℕ->TaggedPartition a b a≤b n .TaggedPartition.t (i , _) =
  (ℚ->ℝ (1/2r + (ℕ->ℚ i))) * (ℚ->ℝ (1/ℕ (suc n , tt))) * (diff a b) + a

ℕ->TaggedPartition a b a≤b n .TaggedPartition.t≤u (i , _) =
  +₂-preserves-≤
   (*₂-preserves-≤ (weaken-<
                     (*₂-preserves-<
                       (ℚ->ℝ-preserves-< _ _ 1/2+i<suc-i)
                       (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))))
                   0≤d)
  where
  0≤d : 0# ≤ (diff a b)
  0≤d = trans-=-≤ (sym +-inverse) (+₂-preserves-≤ a≤b)
  1/2+i<suc-i : (1/2r + (ℕ->ℚ i)) < (ℕ->ℚ (suc i))
  1/2+i<suc-i = trans-<-= (+₂-preserves-< 1/2r<1r) (sym si=1+i)
    where
    si=1+i : ℤ->ℚ (int.int (suc i)) == 1r + ℤ->ℚ (int.int i)
    si=1+i =
      cong ℤ->ℚ (int-inject-+') >=>
      ℤ->ℚ-preserves-+ 1# (int.int i)
ℕ->TaggedPartition a b a≤b n .TaggedPartition.u≤t (i , _) =
  +₂-preserves-≤
   (*₂-preserves-≤ (weaken-<
                     (*₂-preserves-<
                       (ℚ->ℝ-preserves-< _ _ i<1/2+i)
                       (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))))
                   0≤d)
  where
  0≤d : 0# ≤ (diff a b)
  0≤d = trans-=-≤ (sym +-inverse) (+₂-preserves-≤ a≤b)
  i<1/2+i : ℕ->ℚ i < (1/2r + (ℕ->ℚ i))
  i<1/2+i = trans-=-< (sym +-left-zero) (+₂-preserves-< Pos-1/2r)
-- ℕ->TaggedPartition a b a<b n .TaggedPartition.u<u (i , _) =
--   +₂-preserves-<
--     (*₂-preserves-< (*₂-preserves-<
--                       (ℚ->ℝ-preserves-< _ _ i<si)
--                       (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))) 0<d)
--   where
--   0<d : 0# ℝ< (diff a b)
--   0<d = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)
--   i<si : ℕ->ℚ i < ℕ->ℚ (suc i)
--   i<si = ℕ->ℚ-preserves-order i (suc i) refl-≤



isδFinePartition-ℕ->TaggedPartition :
  (a b : ℝ) -> (a≤b : a ≤ b) -> (n : ℕ) ->
  isδFinePartition (ℚ->ℝ (1/ℕ (suc n , tt)) * diff a b) (ℕ->TaggedPartition a b a≤b n)
isδFinePartition-ℕ->TaggedPartition a b a≤b n i = path-≤ tp-width-path
  where
  1/sn = (ℚ->ℝ (1/ℕ (suc n , tt)))
  tp = (ℕ->TaggedPartition a b a≤b n)
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


small-1/ℕ-ℝ : (x : ℝ⁺) -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < ⟨ x ⟩)
small-1/ℕ-ℝ (x , 0<x) = ∥-bind handle 0<x
  where
  handle : 0# ℝ<' x -> ∃[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
  handle (ℝ<'-cons q 0<q q<x) = ∥-map handle2 (small-1/ℕ (q , U->ℚ< 0<q))
    where
    handle2 : Σ[ m ∈ Nat⁺ ] (1/ℕ m) < q ->
              Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < x)
    handle2 (m , 1/m<q) = m , ∣ (ℝ<'-cons q (ℚ<->U 1/m<q) q<x) ∣

∃δFinePartition' :
  {a b : ℝ} -> a ≤ b -> (δ : ℝ⁺) ->
  ∃ (TaggedPartition a b) (isδFinePartition (⟨ δ ⟩ * diff a b))
∃δFinePartition' {a} {b} a≤b (δ , 0<δ) = ∥-map handle (small-1/ℕ-ℝ (δ , 0<δ))
  where
  handle : Σ[ m ∈ Nat⁺ ] (ℚ->ℝ (1/ℕ m) < δ) ->
           Σ (TaggedPartition a b) (isδFinePartition (δ * diff a b))
  handle (((suc n) , _) , 1/n<δ) =
    tp , (weaken-isδFinePartition (*₂-preserves-≤ (weaken-< 1/n<δ) 0≤ab) tp δ-tp)
    where
    tp = ℕ->TaggedPartition a b a≤b n
    δ-tp : isδFinePartition (ℚ->ℝ (1/ℕ (suc n , tt)) * diff a b) tp
    δ-tp = isδFinePartition-ℕ->TaggedPartition a b a≤b n

    0≤ab = trans-=-≤ (sym +-inverse) (+₂-preserves-≤ a≤b)


∃δFinePartition :
  {a b : ℝ} -> a ≤ b -> (δ : ℝ⁺) ->
  ∃ (TaggedPartition a b) (isδFinePartition ⟨ δ ⟩)
∃δFinePartition {a} {b} a≤b (δ , 0<δ) =
  ∥-bind handle (comparison-< 0# ab 1# 0<1)
  where
  ab = diff a b
  handle : ((0# < ab) ⊎ (ab < 1#)) -> ∃ (TaggedPartition a b) (isδFinePartition δ)
  handle (inj-l 0<ab) =
    subst (\δ -> ∃ (TaggedPartition a b) (isδFinePartition δ))
          (*-assoc >=> *-right (ℝ1/-inverse ab (inj-r 0<ab)) >=> *-right-one)
          (∃δFinePartition' a≤b (δ/ab , 0<δ/ab))
    where
    1/ab = ℝ1/ ab (inj-r 0<ab)
    0<1/ab : 0# < 1/ab
    0<1/ab =
      *₂-reflects-<
        (subst2 _<_ (sym *-left-zero) (sym (ℝ1/-inverse ab (inj-r 0<ab))) 0<1)
        0<ab
    δ/ab = δ * 1/ab
    0<δ/ab = *-preserves-0< 0<δ 0<1/ab
  handle (inj-r ab<1) = ∥-map handle2 (∃δFinePartition' a≤b (δ , 0<δ))
    where
    handle2 : Σ (TaggedPartition a b) (isδFinePartition (δ * ab)) ->
              Σ (TaggedPartition a b) (isδFinePartition δ)
    handle2 (tp , δab-tp) = tp , weaken-isδFinePartition δab≤δ tp δab-tp
      where
      δab≤δ = trans-≤-= (weaken-< (*₁-preserves-< 0<δ ab<1)) *-right-one


record isOrderedIntegral' (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  no-eta-equality
  field
    a≤b : a ≤ b
    δε : (ε : ℚ⁺) -> ∃[ δ ∈ ℝ⁺ ] (
           (p : TaggedPartition a b) -> isδFinePartition ⟨ δ ⟩ p ->
           εBounded ⟨ ε ⟩ (diff (riemann-sum f p) v))

data isIntegral' (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) : Type₁ where
  isIntegral'-≤-cons : a ≤ b -> isOrderedIntegral' a b f v -> isIntegral' a b f v
  isIntegral'-≥-cons : a ≥ b -> isOrderedIntegral' b a f (- v) -> isIntegral' a b f v

isIntegral : (a : ℝ) (b : ℝ) (f : ℝ -> ℝ) (v : ℝ) -> Type₁
isIntegral a b f v = ∥ isIntegral' a b f v ∥

isProp-isOrderedIntegral' : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isOrderedIntegral' a b f v)
isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.a≤b =
  isProp-≤ (isOrderedIntegral'.a≤b i1) (isOrderedIntegral'.a≤b i2) i
isProp-isOrderedIntegral' i1 i2 i .isOrderedIntegral'.δε ε =
  squash (isOrderedIntegral'.δε i1 ε) (isOrderedIntegral'.δε i2 ε) i

isProp-isIntegral : {a b : ℝ} {f : ℝ -> ℝ} {v : ℝ} -> isProp (isIntegral a b f v)
isProp-isIntegral = squash


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
  ΣProp-path isProp-isOrderedIntegral' v1=v2
  where
  a≤b = isOrderedIntegral'.a≤b i1
  g : (ε : ℚ⁺) -> εBounded ⟨ ε ⟩ (diff v1 v2)
  g (ε , 0<ε) =
    unsquash (isProp-εBounded ε (diff v1 v2))
      (∥-bind2 handle (isOrderedIntegral'.δε i1 (ε/2 , 0<ε/2)) (isOrderedIntegral'.δε i2 (ε/2 , 0<ε/2)))
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
      ∥-map handle2 (∃δFinePartition a≤b (δ , 0<δ))
      where
      δ = minℝ δ1 δ2
      0<δ = minℝ-<-both 0<δ1 0<δ2

      handle2 : Σ (TaggedPartition a b) (isδFinePartition δ) ->
                εBounded ε (diff v1 v2)
      handle2 (tp , δ-tp) = εB
        where
        εB1 = tp1-f tp (weaken-isδFinePartition (minℝ-≤-left δ1 δ2) tp δ-tp)
        εB2 = tp2-f tp (weaken-isδFinePartition (minℝ-≤-right δ1 δ2) tp δ-tp)
        εB1' = subst (εBounded ε/2) (sym diff-anticommute)
                 (εBounded-- (diff (riemann-sum f tp) v1) εB1)
        εB = subst2 εBounded (1/2r-path' ε) diff-trans
               (εBounded-+ (diff v1 (riemann-sum f tp))
                           (diff (riemann-sum f tp) v2) εB1' εB2)


  v1=v2 : v1 == v2
  v1=v2 = εBounded-diff->path v1 v2 g


-- isOrderedIntegral'-zero-interval : {a : ℝ} {f : ℝ -> ℝ} -> isOrderedIntegral' a a f 0#
-- isOrderedIntegral'-zero-interval {a} {f} .isOrderedIntegral'.a≤b = refl-≤
-- isOrderedIntegral'-zero-interval {a} {f} .isOrderedIntegral'.δε ε⁺@(ε , 0<ε) = ∣ (δ , 0<1) , bound ∣
--   where
--   δ = 1#
--
--   zero-sum : (p : TaggedPartition a a) -> (riemann-sum f p) == 0#
--   zero-sum p = cong finiteSum (funExt zero-term) >=> finiteMerge-ε _
--     where
--     module p = TaggedPartition p
--     u=a : (i : Fin (suc p.n)) -> p.u i == a
--     u=a i = ?
--
--
--     zero-term : (i : Fin p.n) -> p.t i * p.width i == 0#
--     zero-term i = *-right (cong2 diff (u=a _) (u=a _) >=> +-inverse) >=> *-right-zero
--
--
--
--   bound : (p : TaggedPartition a a) -> isδFinePartition δ p ->
--            εBounded ε (diff (riemann-sum f p) 0#)
--   bound p _ = subst (εBounded ε) (sym +-inverse >=> +-left (zero-sum p)) (εBounded-0 ε⁺)
