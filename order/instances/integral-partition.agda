{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.integral-partition where

open import base
open import equality
open import equivalence.base
open import fin
open import fin-algebra
open import fin.list
open import fin.list.sorted
open import hlevel.base
open import isomorphism
open import nat
open import order hiding (_≼_ ; refl-≼ ; trans-≼ ; isProp-≼)
open import order.homomorphism
open import order.homomorphism.fin
open import order.instances.fin
open import order.instances.nat
open import order.instances.rational
open import rational
open import real
open import real.integral.partition
open import real.integral.partition-index
open import real.integral.partition-refinement
open import relation
open import sigma.base
open import truncation
open import univalence

private
  isProp-≼ : {a b : ℝ} {p1 p2 : Partition a b} -> isProp (Partition≼ p1 p2)
  isProp-≼ {p2 = p2} r1 r2 i .Partition≼.refines = isProp-≤ r1.refines r2.refines i
    where
    module r1 = Partition≼ r1
    module r2 = Partition≼ r2

  refl-≼ : {a b : ℝ} {p : Partition a b} -> (Partition≼ p p)
  refl-≼  .Partition≼.refines = refl-≤


  trans-≼ : {a b : ℝ} {p1 p2 p3 : Partition a b} (r1 : Partition≼ p1 p2) (r2 : Partition≼ p2 p3) ->
            Partition≼ p1 p3
  trans-≼ r1 r2 .Partition≼.refines = trans-≤ r1.refines r2.refines
    where
    module r1 = Partition≼ r1
    module r2 = Partition≼ r2

  abstract
    antisym-≼ : {a b : ℝ} {p1 p2 : Partition a b} (r1 : Partition≼ p1 p2) (r2 : Partition≼ p2 p1) ->
                p1 == p2
    antisym-≼ {a} {b} {p1@(record {})} {p2@(record {})} r1 r2 = full-path
      where
      module p1 = Partition p1
      module p2 = Partition p2
      module r1 = Partition≼ r1
      module r2 = Partition≼ r2

      points-path : p1.points == p2.points
      points-path = antisym-≤ r1.refines r2.refines

      u-path : PathP (\i -> Fin (fst (fst (points-path i))) -> ℚ) p1.u p2.u
      u-path i = snd (fst (points-path i))

      n-path : p1.n == p2.n
      n-path i = pred (fst (fst (points-path i)))

      u-path2 : PathP (\i -> Fin (suc (n-path i)) -> ℚ) p1.u p2.u
      u-path2 =
        subst (\sn -> PathP (\i -> Fin (sn i) -> ℚ) p1.u p2.u)
              (isSetNat _ _ _ _) u-path

      module _ where
        u0-path : p1.u zero-fin == p2.u zero-fin
        u0-path i = (u-path2 i) zero-fin

        un-path : p1.u (p1.n , refl-≤) == p2.u (p2.n , refl-≤)
        un-path i = (u-path2 i) (_ , refl-≤)

        a-path : PathP (\pi -> Real.U a (u0-path pi)) p1.aU-u0 p2.aU-u0
        a-path = isProp->PathP (\pi -> Real.isProp-U a (u0-path pi))

        b-path : PathP (\pi -> Real.L b (un-path pi)) p1.bL-un p2.bL-un
        b-path = isProp->PathP (\pi -> Real.isProp-L b (un-path pi))

        u<u-path : PathP (\pi -> (i : Fin (n-path pi)) ->
                                 (u-path2 pi (inc-fin i)) < (u-path2 pi (suc-fin i)))
                          p1.u<u p2.u<u
        u<u-path = isProp->PathP (\pi -> isPropΠ (\i -> isProp-<))

      full-path : p1 == p2
      full-path pi = record
        { n = n-path pi
        ; u = (u-path2 pi)
        ; aU-u0 = a-path pi
        ; bL-un = b-path pi
        ; u<u = u<u-path pi
        }

instance
  isPartialOrder-Partition≼ : {a b : ℝ} -> isPartialOrder (Partition≼ {a} {b})
  isPartialOrder-Partition≼ = record
    { isProp-≤ = isProp-≼
    ; refl-≤ = refl-≼
    ; trans-≤ = trans-≼
    ; antisym-≤ = antisym-≼
    }
