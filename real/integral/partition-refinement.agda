{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition-refinement where

open import base
open import equality
open import fin
open import order
open import order.instances.nat
open import order.instances.rational
open import real
open import real.integral.partition
open import real.integral.partition-index
open import real.rational

record Partition≼ {a b : ℝ} (p1 p2 : Partition a b) : Type₀ where
  constructor Partition≼-cons
  private
    module p1 = Partition p1
    module p2 = Partition p2

  field
    indexes : ∀ (i : Fin (suc p1.n)) -> Σ[ j ∈ Fin (suc p2.n) ] (p1.u i == p2.u j)

  u0≤ : p2.u zero-fin ≤ p1.u zero-fin
  u0≤ = handle (indexes zero-fin)
    where
    handle : Σ[ j ∈ Fin (suc p2.n) ] (p1.u zero-fin == p2.u j) -> p2.u zero-fin ≤ p1.u zero-fin
    handle (j , path) = trans-≤-= (p2.u0≤ui j) (sym path)

  un≤ : p1.u (p1.n , refl-≤) ≤ p2.u (p2.n , refl-≤)
  un≤ = handle (indexes (p1.n , refl-≤))
    where
    handle : Σ[ j ∈ Fin (suc p2.n) ] (p1.u (p1.n , refl-≤) == p2.u j) ->
             p1.u (p1.n , refl-≤) ≤ p2.u (p2.n , refl-≤)
    handle (j , path) = trans-=-≤ path (p2.ui≤un j)

  boundaries : (i : PartitionBoundary p1.n) -> Σ[ j ∈ PartitionBoundary p2.n ] (p1.uB i == p2.uB j)
  boundaries pb-low     = pb-low , refl
  boundaries (pb-mid i) = case (indexes i) of \(j , p) -> pb-mid j , cong ℚ->ℝ p
  boundaries pb-high    = pb-high , refl
