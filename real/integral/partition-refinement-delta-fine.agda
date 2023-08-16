{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition-refinement-delta-fine where

open import additive-group.instances.real
open import base
open import equality
open import fin
open import finset
open import finset.detachable
open import finset.optimize
open import order
open import order.instances.real
open import order.subtype
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import rational
open import real
open import real.integral.partition
open import real.integral.partition-index
open import real.integral.partition-refinement
open import real.rational
open import relation
open import ring.implementations.real
open import subset
open import sum
open import truncation

private
  enclosing :
    {a b : ℝ} {p1 p2 : Partition a b} -> Partition≼ p1 p2 ->
    (i : PartitionIndex (Partition.n p2)) ->
    ∃[ j ∈ PartitionIndex (Partition.n p1) ]
      (Partition.interval-low p1 j ≤ Partition.interval-low p2 i ×
       Partition.interval-high p2 i ≤ Partition.interval-high p1 j)
  enclosing {a} {b} {p1} {p2} r i =
    ∥-map2 handle-bounds maxLowerT minUpperT
    where
    module p1 = Partition p1
    module p2 = Partition p2
    module r = Partition≼ r

    pb-il = ⟨ index->low-boundary i ⟩
    pb-ih = ⟨ index->high-boundary i ⟩

    lower-bound : Subtype (PartitionBoundary p1.n) ℓ-one
    lower-bound j = p1.uB j ≤ p2.uB pb-il , isProp-≤
    upper-bound : Subtype (PartitionBoundary p1.n) ℓ-one
    upper-bound j = p2.uB pb-ih ≤ p1.uB j , isProp-≤

    detach-lower-bound : Detachable lower-bound
    detach-lower-bound pb-low = yes (p2.a≤uB pb-il)
    detach-lower-bound pb-high =
      no (\b≤v -> bot-elim (irrefl-< (trans-≤-< b≤v (p2.low-boundary<b (index->low-boundary i)))))
    detach-lower-bound (pb-mid j) = handle (r.indexes j)
      where
      handle : Σ[ i2 ∈ Fin (suc p2.n) ] (p1.u j == p2.u i2) -> _
      handle (i2 , u-path) = handle2 (split-< pb-il (pb-mid i2))
        where
        handle2 : (pb-il < (pb-mid i2) ⊎ (pb-mid i2) ≤ pb-il) -> _
        handle2 (inj-l lt) = no (\le -> le (trans-<-= (p2.uB-preserves-< lt) (cong ℚ->ℝ (sym u-path))))
        handle2 (inj-r le) = yes (trans-=-≤ (cong ℚ->ℝ u-path) (p2.uB-preserves-≤ le))

    detach-upper-bound : Detachable upper-bound
    detach-upper-bound pb-low =
      no (\v≤a -> bot-elim (irrefl-< (trans-<-≤ (p2.a<high-boundary (index->high-boundary i)) v≤a)))
    detach-upper-bound pb-high = yes (p2.uB≤b pb-ih)
    detach-upper-bound (pb-mid j) = handle (r.indexes j)
      where
      handle : Σ[ i2 ∈ Fin (suc p2.n) ] (p1.u j == p2.u i2) -> _
      handle (i2 , u-path) = handle2 (split-< (pb-mid i2) pb-ih)
        where
        handle2 : ((pb-mid i2) < pb-ih ⊎ pb-ih ≤ (pb-mid i2)) -> _
        handle2 (inj-l lt) = no (\le -> le (trans-=-< (cong ℚ->ℝ u-path) (p2.uB-preserves-< lt)))
        handle2 (inj-r le) = yes (trans-≤-= (p2.uB-preserves-≤ le) (cong ℚ->ℝ (sym u-path)))


    LowerT : Type _
    LowerT = ∈-Subtype lower-bound
    UpperT : Type _
    UpperT = ∈-Subtype upper-bound

    FinSet-LowerT : FinSet _
    FinSet-LowerT = FinSet-Detachable (FinSet-PartitionBoundary _) lower-bound detach-lower-bound
    FinSet-UpperT : FinSet _
    FinSet-UpperT = FinSet-Detachable (FinSet-PartitionBoundary _) upper-bound detach-upper-bound

    inLowerT : LowerT
    inLowerT = pb-low , p2.a≤uB pb-il
    inUpperT : UpperT
    inUpperT = pb-high , p2.uB≤b pb-ih

    instance
      PO-LowerT : isPartialOrder _
      PO-LowerT = isPartialOrder->isPartialOrder-Subtype≤ lower-bound useⁱ
      PO-UpperT : isPartialOrder _
      PO-UpperT = isPartialOrder->isPartialOrder-Subtype≤ upper-bound useⁱ

    maxLowerT : ∃[ v ∈ LowerT ] (∀ (v2 : LowerT) -> v2 ≤ v)
    maxLowerT = handle (finite-argmax FinSet-LowerT fst)
      where
      handle : _ -> _
      handle (inj-l ¬LowerT) = bot-elim (¬LowerT inLowerT)
      handle (inj-r v) = v
    minUpperT : ∃[ v ∈ UpperT ] (∀ (v2 : UpperT) -> v ≤ v2)
    minUpperT = handle (finite-argmin FinSet-UpperT fst)
      where
      handle : _ -> _
      handle (inj-l ¬UpperT) = bot-elim (¬UpperT inUpperT)
      handle (inj-r v) = v

    handle-bounds : Σ[ v ∈ LowerT ] (∀ (v2 : LowerT) -> v2 ≤ v) ->
                    Σ[ v ∈ UpperT ] (∀ (v2 : UpperT) -> v ≤ v2) ->
                    Σ[ j ∈ PartitionIndex p1.n ]
                      (p1.interval-low j ≤ p2.interval-low i ×
                       p2.interval-high i ≤ p1.interval-high j)
    handle-bounds ((low-b , low-b≤) , low-f) ((up-b , up-b≤) , up-f) =
      fst Σj , trans-=-≤ (cong p1.uB (sym (fst (snd Σj)))) low-b≤ ,
               trans-≤-= up-b≤ (cong p1.uB (snd (snd Σj)))
      where
      f : ∀ inner-b -> ¬(low-b < inner-b × inner-b < up-b)
      f inner-b (low<inner , inner<up) =
        handle (split-< pb-il inner2) (split-< inner2 pb-ih)
        where
        Σinner2 : Σ[ j ∈ PartitionBoundary p2.n ] (p1.uB inner-b == p2.uB j)
        Σinner2 = r.boundaries inner-b
        inner2 = fst Σinner2

        handle : (pb-il < inner2 ⊎ inner2 ≤ pb-il) ->
                 (inner2 < pb-ih ⊎ pb-ih ≤ inner2) ->
                  Bot
        handle (inj-r i2≤pb-il) _ =
          irrefl-< (trans-<-≤ low<inner le)
          where
          check : ⟨ lower-bound inner-b ⟩
          check = trans-=-≤ (snd Σinner2) (p2.uB-preserves-≤ i2≤pb-il)

          le : inner-b ≤ low-b
          le = low-f (_ , check)
        handle (inj-l _) (inj-r pb-ih≤i2) =
          irrefl-< (trans-≤-< le inner<up)
          where
          check : ⟨ upper-bound inner-b ⟩
          check = trans-≤-= (p2.uB-preserves-≤ pb-ih≤i2) (sym (snd Σinner2))

          le : up-b ≤ inner-b
          le = up-f (_ , check)
        handle (inj-l pb-il<i2) (inj-l i2<pb-ih) =
          snd (Index->SuccessorOf i) inner2 (pb-il<i2 , i2<pb-ih)


      low<up : low-b < up-b
      low<up = proj-¬r (split-< low-b up-b) ¬up≤low
        where
        ¬up≤low : ¬ (up-b ≤ low-b)
        ¬up≤low up≤low = check check2
          where
          check : p2.uB pb-ih ≤ p2.uB pb-il
          check = trans-≤ up-b≤ (trans-≤ (p1.uB-preserves-≤ up≤low) low-b≤)

          check2 : p2.uB pb-il < p2.uB pb-ih
          check2 = p2.uB-preserves-< (low-boundary<high-boundary i)

      adj : SuccessorOf low-b up-b
      adj = low<up , f

      Σj : Σ[ i ∈ PartitionIndex p1.n ] (low-b == ⟨ index->low-boundary i ⟩ ×
                                         up-b == ⟨ index->high-boundary i ⟩)
      Σj = SuccessorOf->Index adj

abstract
  isδFine-Partition≼ :
    {a b : ℝ} {p1 p2 : Partition a b} -> Partition≼ p1 p2 -> (δ : ℝ) -> isδFine δ p1 -> isδFine δ p2
  isδFine-Partition≼ {a} {b} {p1} {p2} r δ fine = fine2
    where
      module p1 = Partition p1
      module p2 = Partition p2
      module r = Partition≼ r

      fine2 : (i : PartitionIndex p2.n) -> (p2.width i) ≤ δ
      fine2 i = unsquash isProp-≤ (∥-map handle (enclosing r i))
        where
        handle : Σ[ j ∈ PartitionIndex (Partition.n p1) ]
                   (Partition.interval-low p1 j ≤ Partition.interval-low p2 i ×
                    Partition.interval-high p2 i ≤ Partition.interval-high p1 j) ->
                 (p2.width i ≤ δ)
        handle (j , low≤ , high≤) =
          trans-≤ (+-preserves-≤ high≤ (minus-flips-≤ low≤)) (fine j)
