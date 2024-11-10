{-# OPTIONS --cubical --safe --exact-split #-}

module fin.list.sorted where

open import base
open import fin
open import isomorphism
open import fin-algebra
open import univalence
open import fin.list
open import equality
open import hlevel
open import hlevel.order
open import nat
open import nat.order.base
open import order
open import order.homomorphism.fin
open import order.homomorphism
open import order.instances.nat
open import order.instances.fin
open import functions
open import funext
open import relation
open import truncation
open import sum
open import sigma.base

import ordered-set.glist

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}  where
  Sorted : Pred (FinList D) (ℓ-max ℓD ℓ<)
  Sorted (n , f) = LinearOrderʰ f

module _ {ℓD ℓ< : Level} (D : Type ℓD) {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}  where
  SortedList : Type (ℓ-max ℓD ℓ<)
  SortedList = Σ (FinList D) Sorted

module _ {ℓB ℓB< : Level} {B : Type ℓB} {B< : Rel B ℓB<} {{LO : isLinearOrder B<}} where
  _sl∈_ : REL B (SortedList B) ℓB
  b sl∈ (l , s) = b l∈ l

  _sl∈'_ : REL B (SortedList B) ℓB
  b sl∈' (l , s) = b l∈' l

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}  where
  isProp-sl∈' : (d : D) (l : SortedList D) -> isProp (d sl∈' l)
  isProp-sl∈' d (l , s) (i1 , p1) (i2 , p2) =
    ΣProp-path (isSet-LinearlyOrdered D _ _)
      (connected-< (\i1<i2 -> irrefl-path-< (p1 >=> sym p2) (s.preserves-< i1<i2))
                   (\i2<i1 -> irrefl-path-< (p2 >=> sym p1) (s.preserves-< i2<i1)))
    where
    module s = LinearOrderʰ s

  private
    Fin-Indices : ordered-set.glist.Indices ℓ-zero ℓ-zero ℓ-zero
    Fin-Indices = Nat , \n -> (Fin n , record { isLinearOrder-< = useⁱ }) , useⁱ

  Sorted≼ : Rel (SortedList D) (ℓ-max ℓ-zero ℓD)
  Sorted≼ = ordered-set.glist.Sorted≼ Fin-Indices

  module Sorted≼ = ordered-set.glist.Sorted≼ {Idxs = Fin-Indices} {{LO = LO}}

  module _ {s1 s2 : SortedList D} where
    private
      l1 = ⟨ s1 ⟩
      l2 = ⟨ s2 ⟩
      n1 = ⟨ l1 ⟩
      n2 = ⟨ l2 ⟩
      f1 = snd l1
      f2 = snd l2

    antisym-Sorted≼ : Sorted≼ s1 s2 -> Sorted≼ s2 s1 -> s1 == s2
    antisym-Sorted≼ r12 r21 = ΣProp-path isProp-LinearOrderʰ l1=l2
      where
      module r12 = Sorted≼ r12
      module r21 = Sorted≼ r21

      n-path : n1 == n2
      n-path = isInjective-Fin (ua (isoToEquiv n-iso))
        where
        n-iso : Iso (Fin n1) (Fin n2)
        n-iso .Iso.fun i = fst (r12.indexes i)
        n-iso .Iso.inv i = fst (r21.indexes i)
        n-iso .Iso.rightInv i = LinearOrderʰᵉ.injective (snd s2) f-path
          where
          f-path : f2 (fst (r12.indexes (fst (r21.indexes i)))) == f2 i
          f-path = sym (snd (r21.indexes i) >=> (snd (r12.indexes (fst (r21.indexes i)))))
        n-iso .Iso.leftInv i = LinearOrderʰᵉ.injective (snd s1) f-path
          where
          f-path : f1 (fst (r21.indexes (fst (r12.indexes i)))) == f1 i
          f-path = sym (snd (r12.indexes i) >=> (snd (r21.indexes (fst (r12.indexes i)))))

      f-paths : (j : Nat) -> (lt1 : j < n1) -> (lt2 : j < n2) -> f1 (j , lt1) == f2 (j , lt2)
      f-paths j lt1 lt2 = sym ans
        where
        module h1 = LinearOrderʰᵉ (snd s1)
        module h2 = LinearOrderʰᵉ (snd s2)

        j1 : Fin n1
        j1 = (j , lt1)
        j2 : Fin n2
        j2 = (j , lt2)

        r2' : Fin n2 -> Fin n1
        r2' i = fst (r21.indexes i)

        r2'< : {x y : Fin n2} -> x < y -> r2' x < r2' y
        r2'< {x} {y} x<y = h1.reflects-< frx<fry
          where
          ux<uy : f2 x < f2 y
          ux<uy = h2.preserves-< x<y

          path1 : f2 x == f1 (r2' x)
          path1 = snd (r21.indexes x)

          path2 : f2 y == f1 (r2' y)
          path2 = snd (r21.indexes y)

          frx<fry : f1 (r2' x) < f1 (r2' y)
          frx<fry = subst2 _<_ path1 path2 ux<uy

        ∃!lh : ∃! (Fin n2 -> Fin n1) LinearOrderʰ
        ∃!lh = ∃!LinearOrderʰ-Fin-Fin' (sym n-path)

        r2'=lh : r2' == (fst (fst ∃!lh))
        r2'=lh = cong fst (sym (snd ∃!lh (r2' , record { preserves-< = r2'< })))

        ans : f2 j2 == f1 j1
        ans =
          (snd (r21.indexes j2)) >=>
          (\i -> f1 ((r2'=lh i) j2)) >=>
          cong f1 (fin-i-path refl)


      l1=l2 : l1 == l2
      l1=l2 = \i -> n-path i , element-paths->vector-path n-path f-paths i

  instance
    isPartialOrder-SortedList : isPartialOrder _
    isPartialOrder-SortedList =
      PartialOrderStr.isPartialOrder-≤
        (ordered-set.glist.PartialOrderStr-SortedList Fin-Indices antisym-Sorted≼)
