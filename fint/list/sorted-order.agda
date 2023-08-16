{-# OPTIONS --cubical --safe --exact-split #-}

module fint.list.sorted-order where

open import base
open import equality
open import equivalence
open import fin-algebra
open import fint.list
open import fint.list.equality
open import fint.list.sorted
open import fint.same-index
open import functions
open import funext
open import hlevel.base
open import hlevel.order
open import isomorphism
open import order
open import order.homomorphism
open import order.homomorphism.fint
open import order.instances.fint
open import relation
open import sigma.base
open import truncation
open import univalence

import ordered-set.glist


module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}  where
  private
    FinT-Indices : ordered-set.glist.Indices ℓ-zero ℓ-zero ℓ-zero
    FinT-Indices = Nat , \n -> (FinT n , record {isLinearOrder-< = useⁱ}) , useⁱ

  Sorted≼ : Rel (SortedList D) (ℓ-max ℓ-zero ℓD)
  Sorted≼ = ordered-set.glist.Sorted≼ FinT-Indices

  module Sorted≼ = ordered-set.glist.Sorted≼ {Idxs = FinT-Indices} {{LO = LO}}

  private

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
        n-path = (FinT-injective (ua (isoToEquiv n-iso)))
          where
          n-iso : Iso (FinT n1) (FinT n2)
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

        f-paths : (i : FinT n1) (j : FinT n2) -> SameIndex i j -> f1 i == f2 j
        f-paths i j si-i-j = ans
          where
          module h1 = LinearOrderʰᵉ (snd s1)
          module h2 = LinearOrderʰᵉ (snd s2)

          r2' : FinT n2 -> FinT n1
          r2' i = fst (r21.indexes i)

          r2'< : {x y : FinT n2} -> x < y -> r2' x < r2' y
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

          r2ʰ : LinearOrderʰ r2'
          r2ʰ = record { preserves-< = r2'< }

          si-j-r2j : SameIndex j (r2' j)
          si-j-r2j = LinearOrderʰ-FinT-FinT'-SameIndex (sym n-path) r2ʰ j

          i=r2j : i == (r2' j)
          i=r2j = SameIndex-path _ _ (trans-SameIndex {i = i} {j = j} {k = r2' j} si-i-j si-j-r2j)

          ans : f1 i == f2 j
          ans = cong f1 i=r2j >=> sym (snd (r21.indexes j))

        l1=l2 : l1 == l2
        l1=l2 = \i -> n-path i , element-paths->vector-path n-path f-paths i

  instance
    isPartialOrder-SortedList : isPartialOrder _
    isPartialOrder-SortedList =
      PartialOrderStr.isPartialOrder-≤
        (ordered-set.glist.PartialOrderStr-SortedList FinT-Indices antisym-Sorted≼)

  empty-Sorted≼ : {l : SortedList D} -> sortedlist-empty ≤ l
  empty-Sorted≼ .Sorted≼.indexes ()


  Contains->Sorted≼ : {l1 l2 : SortedList D} -> (∀ d -> d sl∈ l1 -> d sl∈ l2) -> l1 ≤ l2
  Contains->Sorted≼ {l1} {l2} = SortedList-Ind P pE pC l1
    where
    P : Pred (SortedList D) _
    P l1 = (∀ d -> d sl∈ l1 -> d sl∈ l2) -> l1 ≤ l2

    pE : P sortedlist-empty
    pE _ = empty-Sorted≼

    pC : (d : D) -> (l : SortedList D) -> (lb : LowerBound< ⟨ l ⟩ d) ->
         (P l) -> P (sortedlist-cons d l lb)
    pC d l lb pl d∈s .Sorted≼.indexes (inj-l _) = fst d∈l2 , sym (snd d∈l2)
      where
      d∈l2 : d sl∈' l2
      d∈l2 = unsquash (isProp-sl∈' d l2) (d∈s d ∣ inj-l tt , refl ∣)
    pC d l lb pl d∈s .Sorted≼.indexes (inj-r i) = l≤l2 .Sorted≼.indexes i
      where
      l≤l2 : l ≤ l2
      l≤l2 = pl (\d d∈l -> d∈s d (∥-map (\(i , p) -> inj-r i , p) d∈l))
