{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module fint.list.sorted-merge where

open import base
open import equality
open import equivalence
open import fint.list
open import fint.list.sorted
open import fint.list.sorted-order
open import functions
open import hlevel
open import lattice
open import isomorphism
open import order
open import order.homomorphism
open import order.instances.fint
open import relation
open import sigma.base
open import sum
open import truncation
open import type-algebra

module _ {ℓA ℓ< : Level} {A : Type ℓA} {A< : Rel A ℓ<} {{LO : isLinearOrder A<}}
         {{DLO : DecidableLinearOrderStr LO}} where
  private
    module _ where
      private
        P : (a : A) -> (l : SortedList A) -> Type _
        P a l = Σ[ al ∈ SortedList A ] (∀ a2 -> (a2 sl∈ al) ≃ (∥ a2 sl∈ l ⊎ a2 == a ∥))

      sorted-insert : (a : A) -> (l : SortedList A) -> P a l
      sorted-insert a = SortedList-Ind (P a) pE pC
        where
        pE : P a sortedlist-empty
        pE = (l , s) , eq
          where
          l : FinList A
          l = (1 , \_ -> a)
          s : Sorted l
          s .LinearOrderʰ.preserves-< (finT<-lr {j = ()})
          s .LinearOrderʰ.preserves-< (finT<-rr ())

          eq : (a2 : A) -> a2 l∈ l ≃ (∥ a2 l∈ finlist-empty ⊎ a2 == a ∥)
          eq a2 = isoToEquiv (isProp->iso (∥-map forward) (∥-map backward) squash squash)
            where
            forward : a2 l∈' l -> a2 l∈ finlist-empty ⊎ a2 == a
            forward (i , p) = inj-r (sym p)
            backward : (a2 l∈ finlist-empty ⊎ a2 == a) -> a2 l∈' l
            backward (inj-l a2∈empty) =
              bot-elim (unsquash isPropBot (∥-map (\()) a2∈empty))
            backward (inj-r p) = inj-l tt , sym p

        pC : (a2 : A) (l : SortedList A) (lb : LowerBound< ⟨ l ⟩ a2) ->
             P a l -> P a (sortedlist-cons a2 l lb)
        pC a2 l a2<l ((al , s-al), eq) = handle (trichotomous-< a a2)
          where
          handle : Tri< a a2 -> P a (sortedlist-cons a2 l a2<l)
          handle (tri> _ _ a2<a) = l' , eq'
            where
            a2<al : LowerBound< al a2
            a2<al {a3} a3∈al = unsquash isProp-< (∥-map handle2 (eqFun (eq a3) a3∈al))
              where
              handle2 : a3 sl∈ l ⊎ a3 == a -> a2 < a3
              handle2 (inj-l a3∈l) = a2<l a3∈l
              handle2 (inj-r a3=a) = trans-<-= a2<a (sym a3=a)

            l' : SortedList A
            l' = (sortedlist-cons a2 (al , s-al) a2<al)

            eq' : (a3 : A) -> a3 l∈ ⟨ l' ⟩ ≃ (∥ a3 l∈ (finlist-cons a2 ⟨ l ⟩) ⊎ a3 == a ∥)
            eq' a3 =
              (finlist-cons-l∈-eq a2 al a3) >eq>
              ∥-eq (⊎-equiv (eq a3) (idEquiv _)) >eq>
              ∥-⊎-left-eq >eq>
              ∥-eq (⊎-assoc-eq _ _ _ >eq> (⊎-equiv (idEquiv _) ⊎-flip-eq) >eq>
                    equiv⁻¹ (⊎-assoc-eq _ _ _)) >eq>
              equiv⁻¹ ∥-⊎-left-eq >eq>
              ∥-eq (⊎-equiv (equiv⁻¹ (finlist-cons-l∈-eq a2 ⟨ l ⟩ a3))
                            (idEquiv _))

          handle (tri= _ a=a2 _) = l' , eq'
            where
            l' = (al , s-al)

            eq' : (a3 : A) -> a3 l∈ ⟨ l' ⟩ ≃ (∥ a3 l∈ (finlist-cons a2 ⟨ l ⟩) ⊎ a3 == a ∥)
            eq' a3 = eq a3 >eq>
                     isoToEquiv (isProp->iso (∥-map forward) (∥-bind backward) squash squash)
              where
              forward : a3 l∈ ⟨ l ⟩ ⊎ a3 == a -> a3 l∈ (finlist-cons a2 ⟨ l ⟩) ⊎ a3 == a
              forward (inj-l c) = inj-l (∥-map (\(i , p) -> inj-r i , p) c)
              forward (inj-r p) = (inj-r p)
              backward : a3 l∈ (finlist-cons a2 ⟨ l ⟩) ⊎ a3 == a -> (∥ a3 l∈ ⟨ l ⟩ ⊎ a3 == a ∥)
              backward (inj-l c) =
                (∥-map (⊎-map (idfun _) (\p -> p >=> sym a=a2)) ∘
                 eqFun (finlist-cons-l∈-eq a2 ⟨ l ⟩ a3)) c
              backward (inj-r p) = ∣ (inj-r p) ∣

          handle (tri< a<a2 _ _) = l'2 , eq'
            where
            l'1 : SortedList A
            l'1 = (sortedlist-cons a2 l a2<l)

            a<l'1 : LowerBound< ⟨ l'1 ⟩ a
            a<l'1 {a3} c = unsquash isProp-< (∥-map handle2 c)
              where
              handle2 : a3 sl∈' l'1 -> a < a3
              handle2 (inj-l tt , p) = trans-<-= a<a2 p
              handle2 (inj-r i , p) = trans-< a<a2 (a2<l ∣ (i , p) ∣)

            l'2 : SortedList A
            l'2 = (sortedlist-cons a l'1 a<l'1)

            eq' : (a3 : A) -> a3 l∈ ⟨ l'2 ⟩ ≃ (∥ a3 l∈ (finlist-cons a2 ⟨ l ⟩) ⊎ a3 == a ∥)
            eq' a3 = (finlist-cons-l∈-eq a ⟨ l'1 ⟩ a3)

    module _ where
      private
        P : (l1 : FinList A) -> (l2 : SortedList A) -> Type _
        P l1 l2 = Σ[ l3 ∈ SortedList A ] (∀ a -> (a sl∈ l3) ≃ (∥ a l∈ l1 ⊎ a sl∈ l2 ∥))

        multi-insert : (l2 : SortedList A) (l1 : FinList A) -> P l1 l2
        multi-insert l2 = FinList-Ind (\l1 -> P l1 l2) pE pC
          where
          pE : P finlist-empty l2
          pE = l2 , eq'
            where
            eq' : (a : A) -> _
            eq' a =
              equiv⁻¹ (∥-Prop-eq squash) >eq>
              ∥-eq (equiv⁻¹ (⊎-Bot-eq _) >eq>
                    ⊎-equiv (equiv⁻¹ (finlist-empty-l∈-eq a)) (idEquiv _))

          pC : (a : A) -> (l : FinList A) -> (P l l2) -> P (finlist-cons a l) l2
          pC a l1 (l3 , eq3) = l4 , eq'
            where
            Σl4 = sorted-insert a l3
            l4 = fst Σl4
            eq4 = snd Σl4

            eq' : (a2 : A) -> (a2 sl∈ l4) ≃ (∥ a2 l∈ (finlist-cons a l1) ⊎ a2 sl∈ l2 ∥)
            eq' a2 =
              eq4 a2 >eq>
              ∥-eq (⊎-equiv (eq3 a2) (idEquiv _)) >eq>
              ∥-⊎-left-eq >eq>
              ∥-eq (⊎-assoc-eq _ _ _ >eq>
                    ⊎-equiv (idEquiv _) ⊎-flip-eq >eq>
                    equiv⁻¹ (⊎-assoc-eq _ _ _)) >eq>
              equiv⁻¹ ∥-⊎-left-eq >eq>
              ∥-eq (⊎-equiv (equiv⁻¹ (finlist-cons-l∈-eq a l1 a2)) (idEquiv _))


      multi-insert' : (l1 l2 : SortedList A) ->
                      Σ[ l3 ∈ SortedList A ] (∀ a -> (a sl∈ l3) ≃ (∥ a sl∈ l1 ⊎ a sl∈ l2 ∥))
      multi-insert' (l1 , _) l2 = multi-insert l2 l1

    module _ where
      isProp-merged :
        (l1 l2 : SortedList A) ->
        isProp (Σ[ l3 ∈ SortedList A ] (∀ a -> (a sl∈ l3) ≃ (∥ a sl∈ l1 ⊎ a sl∈ l2 ∥)))
      isProp-merged l1 l2 (l3 , p3) (l4 , p4) =
        ΣProp-path (isPropΠ (\a -> isProp-≃ squash squash)) (antisym-≤ l3≤l4 l4≤l3)
        where
        ∈-eq : ∀ a -> (a sl∈ l3 ≃ a sl∈ l4)
        ∈-eq a = p3 a >eq> (equiv⁻¹ (p4 a))
        l3≤l4 : l3 ≤ l4
        l3≤l4 = Contains->Sorted≼ (\a -> eqFun (∈-eq a))
        l4≤l3 : l4 ≤ l3
        l4≤l3 = Contains->Sorted≼ (\a -> eqInv (∈-eq a))

  sorted-merge : (l1 l2 : SortedList A) ->
                 ∃![ l3 ∈ SortedList A ] (∀ a -> (a sl∈ l3) ≃ (∥ a sl∈ l1 ⊎ a sl∈ l2 ∥))
  sorted-merge l1 l2 = multi-insert' l1 l2 , isProp-merged l1 l2 _


  sorted-join : JoinSemiLatticeStr (getⁱ (isPartialOrder {D = (SortedList A)} _))
  sorted-join = record
    { join = \l1 l2 -> ∃!-val (sorted-merge l1 l2)
    ; is-join-op = record
      { join-≤-left = \{l1} {l2} -> 1≤3 l1 l2
      ; join-≤-right = \{l1} {l2} -> 2≤3 l1 l2
      ; join-least-≤ = \{l1} {l2} -> least3 l1 l2
      }
    }
    where
    module _ (l1 l2 : SortedList A) where
      ∃!l3 = sorted-merge l1 l2
      l3 = ∃!-val ∃!l3
      1≤3 : l1 ≤ l3
      1≤3 = Contains->Sorted≼ (\ a a∈l1 -> eqInv (∃!-prop ∃!l3 a) ∣ inj-l a∈l1 ∣)
      2≤3 : l2 ≤ l3
      2≤3 = Contains->Sorted≼ (\ a a∈l2 -> eqInv (∃!-prop ∃!l3 a) ∣ inj-r a∈l2 ∣)
      least3 : {l4 : SortedList A} -> l1 ≤ l4 -> l2 ≤ l4 -> l3 ≤ l4
      least3 {l4} 1≤4 2≤4 = Contains->Sorted≼ (\a a∈l3 -> ∥-bind handle (eqFun (∃!-prop ∃!l3 a) a∈l3))
        where
        handle : {a : A} -> (a sl∈ l1 ⊎ a sl∈ l2) -> a sl∈ l4
        handle (inj-l a∈l1) = Sorted≼.preserves-∈ 1≤4 a∈l1
        handle (inj-r a∈l2) = Sorted≼.preserves-∈ 2≤4 a∈l2
