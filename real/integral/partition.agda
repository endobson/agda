{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import fin
open import nat
open import nat.order
open import order
open import ordered-semiring
open import ordered-semiring.instances.real
open import order.instances.nat
open import order.instances.real
open import real
open import relation

record Partition (a : ℝ) (b : ℝ) : Type₁ where
  no-eta-equality
  pattern
  field
    n : ℕ
    u : Fin (suc n) -> ℝ
    u0=a : u zero-fin == a
    un=b : u (n , refl-≤) == b
    u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)

  width : (i : Fin n) -> ℝ
  width i = (diff (u (inc-fin i)) (u (suc-fin i)))

  abstract
    a≤ui : (i : Fin (suc n)) -> a ≤ u i
    a≤ui (i , lt) = handle i lt
      where
      handle : (i : Nat) -> (lt : i < suc n) -> a ≤ u (i , lt)
      handle zero lt = path-≤ (sym u0=a >=> cong u (fin-i-path refl))
      handle (suc i) lt =
        trans-≤ (handle i (trans-< refl-≤ lt))
                (subst2 _≤_ (cong u (fin-i-path refl)) (cong u (fin-i-path refl))
                            (weaken-< (u<u (i , pred-≤ lt))))

    ui≤b : (i : Fin (suc n)) -> u i ≤ b
    ui≤b (i , j , path) = handle i j path
      where
      handle : (i j : Nat) -> (p : j + (suc i) == (suc n)) -> u (i , j , p) ≤ b
      handle i zero path = path-≤ (cong u (fin-i-path (cong pred path)) >=> un=b)
      handle i (suc j) path =
        trans-≤ (subst2 _≤_ (cong u (fin-i-path refl)) (cong u (fin-i-path refl))
                            (weaken-< (u<u (i , j , cong pred path))))
                (handle (suc i) j (+'-right-suc >=> path))

    0<width : (i : Fin n) -> 0# < width i
    0<width i = trans-=-< (sym +-inverse) (+₂-preserves-< (u<u i))



PartitionSize< : {a b : ℝ} -> Rel (Partition a b) ℓ-zero
PartitionSize< p1 p2 = Partition.n p1 < Partition.n p2

WF-PartitionSize< : {a b : ℝ} -> WellFounded (PartitionSize< {a} {b})
WF-PartitionSize< {a} {b} p = rec p (Partition.n p) refl-≤
  where
  rec : (p : Partition a b) -> (n : Nat) -> (Partition.n p) ≤ n -> Acc PartitionSize< p
  rec p@(record {n = zero})    _    _  = acc (\y yn<0 -> bot-elim (zero-≮ yn<0))
  rec p@(record {n = (suc n)}) zero lt = bot-elim (zero-≮ lt)
  rec p@(record {n = (suc n)}) (suc n') lt =
    acc \p2 p2n<pn -> rec p2 n' (pred-≤ (trans-≤ p2n<pn lt))


partition->≤ : {a b : ℝ} -> Partition a b -> a ≤ b
partition->≤ {a} {b} p = handle (WF-PartitionSize< p)
  where
  handle : {p : Partition a b} -> Acc PartitionSize< p -> a ≤ b
  handle {p@(record {n = zero})} (acc f) =
    path-≤ (
      sym (Partition.u0=a p) >=>
      cong (Partition.u p) (fin-i-path refl) >=>
      (Partition.un=b p))
  handle {p@(record {n = (suc zero); u = u; u0=a = u0=a; un=b = un=b; u<u = u<u})} (acc f) =
   (subst2 _≤_ (cong u (fin-i-path refl) >=> u0=a) (cong u (fin-i-path refl) >=> un=b)
          (weaken-< (u<u zero-fin)))

  handle {p@(record {n = (suc (suc n)); u = u; u0=a = u0=a; un=b = un=b; u<u = u<u})} (acc f) =
    handle (f p2 refl-≤)
    where
    u' : Fin (suc (suc n)) -> ℝ
    u' (zero , _) = u zero-fin
    u' i@(suc n , _) = u (suc-fin i)

    u'<u' : (i : Fin (suc n)) -> u' (inc-fin i) < u' (suc-fin i)
    u'<u' i@(zero , _) =
      trans-< (subst2 _<_ (cong u (fin-i-path refl)) refl (u<u (inc-fin i)))
              (subst2 _<_ (cong u (fin-i-path refl)) refl (u<u (suc-fin i)))
    u'<u' i@(suc n , _) = subst2 _<_ (cong u (fin-i-path refl)) refl (u<u (suc-fin i))

    p2 : Partition a b
    p2 = record
      { n = (suc n)
      ; u = u'
      ; u0=a = u0=a
      ; un=b = cong u (fin-i-path refl) >=> un=b
      ; u<u = u'<u'
      }

isδFine : {a b : ℝ} (δ : ℝ) (p : Partition a b) -> Type₁
isδFine δ p = (i : Fin p.n) -> p.width i ≤ δ
  where
  module p = Partition p

weaken-isδFine : {a b : ℝ} {δ1 δ2 : ℝ} -> δ1 ≤ δ2 -> (p : Partition a b) ->
                          isδFine δ1 p -> isδFine δ2 p
weaken-isδFine δ1≤δ2 _ f i = trans-≤ (f i) δ1≤δ2
