{-# OPTIONS --cubical --safe --exact-split #-}

module fin.list.sorted-merge where

open import base
open import cubical
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import fin.list.sorted
open import hlevel
open import lattice
open import order
open import order.instances.fin
open import order.instances.fint
open import ordered-set
open import ordered-set.fin
open import relation
open import sigma.base
open import truncation

import fint.list.sorted
import fint.list.sorted-order
import fint.list.sorted-merge
import ordered-set.glist as glist


module _ {ℓA ℓ< : Level} {A : Type ℓA} {LO : LinearOrderStr A ℓ<}
         {{DLO : DecidableLinearOrderStr LO}} where
  private
    instance
      ILO = LO

    indices-path : Path (glist.Indices ℓ-zero ℓ-zero ℓ-zero)
                    (Nat , (\n -> (FinT n , useⁱ) , useⁱ))
                    (Nat , (\n -> (Fin n , useⁱ) , useⁱ))
    indices-path = Indices-FinT=Fin

    type-path : (fint.list.sorted.SortedList A) == (SortedList A)
    type-path = (\i -> glist.SortedList (indices-path i) A)


  abstract
    sorted-merge : (l1 l2 : SortedList A) ->
                   ∃![ l3 ∈ SortedList A ] (∀ a -> (a sl∈ l3) ≃ (∥ a sl∈ l1 ⊎ a sl∈ l2 ∥))
    sorted-merge =
      subst (\i -> (l1 l2 : glist.SortedList i A) ->
                   ∃![ l3 ∈ glist.SortedList i A ]
                     (∀ a -> (a glist.l∈ ⟨ l3 ⟩) ≃
                             (∥ a glist.l∈ ⟨ l1 ⟩ ⊎ a glist.l∈ ⟨ l2 ⟩ ∥)))
            indices-path
            fint.list.sorted-merge.sorted-merge

    instance
      sorted-join : JoinSemiLatticeStr (getⁱ (PartialOrderStr (SortedList A) ℓA))
      sorted-join = subst hasJoin path fint.list.sorted-merge.sorted-join
        where
        module _ where
          <-path : PathP (\i -> (type-path i) -> (type-path i) -> _) _≤_ _≤_
          <-path = (\i -> glist.Sorted≼ (indices-path i))

          po-path : PathP (\i -> isPartialOrder (<-path i))
                          (PartialOrderStr.isPartialOrder-≤ useⁱ)
                          (PartialOrderStr.isPartialOrder-≤ useⁱ)
          po-path = isProp->PathP (\i -> isProp-isPartialOrder _)

          order-path : PathP (\i -> PartialOrderStr (type-path i) _) useⁱ useⁱ
          order-path i = record
            { _≤_ = <-path i
            ; isPartialOrder-≤ = po-path i
            }

          path : Path (POSet (ℓ-max ℓA (ℓ-suc ℓ<)) ℓA)
                      ((fint.list.sorted.SortedList A) , useⁱ)
                      ((SortedList A) , useⁱ)
          path i = type-path i , order-path i

          hasJoin : {ℓA ℓ< : Level} -> Pred (POSet ℓA ℓ<) (ℓ-max ℓA ℓ<)
          hasJoin (_ , PO) = JoinSemiLatticeStr PO
