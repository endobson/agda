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


module _ {ℓD ℓ< : Level} {D : Type ℓD} {{LO : LinearOrderStr D ℓ<}}  where

  private
    SubSequenceIndexes : Rel (FinList D) _
    SubSequenceIndexes (n1 , f1) (n2 , f2) =
      ∀ (x : FinT n1) -> Σ[ y ∈ FinT n2 ] f1 x == f2 y

    isProp-Sorted-SubSequenceIndexes : (s1 s2 : SortedList D) ->
                                       isProp (SubSequenceIndexes ⟨ s1 ⟩ ⟨ s2 ⟩)
    isProp-Sorted-SubSequenceIndexes ((n1 , f1) , s1) ((n2 , f2) , s2) r1 r2 = funExt r3
      where
      r3 : ∀ (i : FinT n1) -> r1 i == r2 i
      r3 i =
        ΣProp-path (isSet-LinearlyOrdered D _ _)
          (connected-< (\i1<i2 -> irrefl-path-< (sym (snd (r1 i)) >=> (snd (r2 i)))
                                                (s2.preserves-< i1<i2))
                       (\i2<i1 -> irrefl-path-< (sym (snd (r2 i)) >=> (snd (r1 i)))
                                                (s2.preserves-< i2<i1)))
        where
        module s2 = LinearOrderʰ s2

    SubSequence≃Indexes : (s1 s2 : SortedList D) ->
                          SubSequence ⟨ s1 ⟩ ⟨ s2 ⟩ ≃ SubSequenceIndexes ⟨ s1 ⟩ ⟨ s2 ⟩
    SubSequence≃Indexes sl1@(l1@(n1 , f1) , s1) sl2@(l2@(n2 , f2) , s2) =
      isoToEquiv (isProp->iso (unsquash isProp-SSSI ∘ ∥-map forward) backward
                              squash isProp-SSSI)
      where
      module s1 = LinearOrderʰ s1
      module s2 = LinearOrderʰ s2

      isProp-SSSI = (isProp-Sorted-SubSequenceIndexes sl1 sl2)
      forward : Σ[ g ∈ (FinT n1 -> FinT n2) ] (LinearOrderʰ g × ∀ i -> (f1 i) == (f2 (g i))) ->
                SubSequenceIndexes l1 l2
      forward (g , (_ , p)) = \i -> g i , p i
      backward : SubSequenceIndexes l1 l2 -> SubSequence l1 l2
      backward g = ∣ g' , gʰ , (\i -> snd (g i)) ∣
        where
        g' : FinT n1 -> FinT n2
        g' i = fst (g i)
        gʰ : LinearOrderʰ g'
        gʰ .LinearOrderʰ.preserves-< {i} {j} i<j =
          s2.reflects-< (subst2 _<_ p1 p2 (s1.preserves-< i<j))
          where
          p1 : f1 i == f2 (g' i)
          p1 = snd (g i)
          p2 : f1 j == f2 (g' j)
          p2 = snd (g j)

  record Sorted≼ (s1 s2 : SortedList D) : Type (ℓ-max ℓ-one ℓD) where
    private
      l1 = ⟨ s1 ⟩
      l2 = ⟨ s2 ⟩

    field
      indexes : SubSequenceIndexes l1 l2

    subsequence : SubSequence l1 l2
    subsequence = eqInv (SubSequence≃Indexes s1 s2) indexes

    preserves-∈ : {d : D} -> d l∈ l1 -> d l∈ l2
    preserves-∈ =
      ∥-map (\ (i , p) -> fst (indexes i) , sym (snd (indexes i)) >=> p)


  private
    refl-Sorted≼ : {s1 : SortedList D} -> Sorted≼ s1 s1
    refl-Sorted≼ .Sorted≼.indexes i = i , refl

    trans-Sorted≼ : {s1 s2 s3 : SortedList D} -> Sorted≼ s1 s2 -> Sorted≼ s2 s3 -> Sorted≼ s1 s3
    trans-Sorted≼ r12 r23 .Sorted≼.indexes i1 = ⟨ Σi3 ⟩ , snd Σi2 >=> snd Σi3
      where
      Σi2 = Sorted≼.indexes r12 i1
      Σi3 = Sorted≼.indexes r23 ⟨ Σi2 ⟩

    module _ {s1 s2 : SortedList D} where
      private
        l1 = ⟨ s1 ⟩
        l2 = ⟨ s2 ⟩
        n1 = ⟨ l1 ⟩
        n2 = ⟨ l2 ⟩
        f1 = snd l1
        f2 = snd l2

      isProp-Sorted≼ : (r1 r2 : Sorted≼ s1 s2) -> r1 == r2
      isProp-Sorted≼ r1 r2 i .Sorted≼.indexes =
        isPropΠ isProp-index (Sorted≼.indexes r1) (Sorted≼.indexes r2) i
        where
        isProp-index : (x : FinT n1) -> isProp (Σ[ y ∈ FinT n2 ] f1 x == f2 y)
        isProp-index x (y1 , p1) (y2 , p2) =
          ΣProp-path (isSet-LinearlyOrdered D _ _) (LinearOrderʰᵉ.injective (snd s2) (sym p1 >=> p2))


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
    PartialOrderStr-SortedList : PartialOrderStr (SortedList D) _
    PartialOrderStr-SortedList = record
      { _≤_ = Sorted≼
      ; isPartialOrder-≤ = record
        { isProp-≤ = isProp-Sorted≼
        ; refl-≤ = refl-Sorted≼
        ; trans-≤ = trans-Sorted≼
        ; antisym-≤ = antisym-Sorted≼
        }
      }

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
