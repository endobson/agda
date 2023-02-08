{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-set.glist where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import functions
open import funext
open import hlevel
open import hlevel.order
open import isomorphism
open import order
open import order.homomorphism
open import order.instances.fin
open import order.instances.fint
open import ordered-set
open import relation
open import sigma.base
open import truncation
open import univalence

Indices : (ℓS ℓI ℓ< : Level) -> Type _
Indices ℓS ℓI ℓ< = Σ[ S ∈ Type ℓS ] (S -> Σ[ LO ∈ LOSet ℓI ℓ< ] (DecidableLinearOrderStr (snd LO)))

Container : {ℓS ℓI ℓA : Level} {S : Type ℓS} -> (S -> Type ℓI) -> Type ℓA -> Type (ℓ-max* 3 ℓI ℓA ℓS)
Container {S = S} I A = Σ[ s ∈ S ] (I s -> A)

Vector : {ℓI ℓ< ℓA : Level} -> (LOSet ℓI ℓ<) -> Type ℓA -> Type (ℓ-max ℓI ℓA)
Vector (I , _) A = I -> A

List : {ℓS ℓI ℓ< ℓA : Level} -> Indices ℓS ℓI ℓ< -> Type ℓA -> Type (ℓ-max* 3 ℓI ℓA ℓS)
List (S , I) A = Σ[ s ∈ S ] (Vector ⟨ I s ⟩ A)

SubSequence : {ℓS ℓI ℓ< ℓA : Level} {A : Type ℓA} -> (I : Indices ℓS ℓI ℓ<) -> Rel (List I A) _
SubSequence (S , I) (s1 , f1) (s2 , f2) =
  ∃[ g ∈ (I' s1 -> I' s2) ] (
    LinearOrderʰᵉ (snd (fst (I s1))) (snd (fst (I s2))) g ×
    ∀ i -> (f1 i) == (f2 (g i)))
  where
  I' = fst ∘ fst ∘ I

_l∈'_ : {ℓS ℓI ℓA : Level} {S : Type ℓS} {I : S -> Type ℓI} {A : Type ℓA} ->
        REL A (Container I A) _
_l∈'_ {I = I} a (s , f) = Σ[ i ∈ I s ] (f i == a)

_l∈_ : {ℓS ℓI ℓA : Level} {S : Type ℓS} {I : S -> Type ℓI} {A : Type ℓA} ->
       REL A (Container I A) _
_l∈_ a l = ∥ a l∈' l ∥

module _ {ℓD ℓ< : Level} {D : Type ℓD} {{LO : LinearOrderStr D ℓ<}}  where
  Sorted : {ℓS ℓI ℓI< : Level} -> (I : Indices ℓS ℓI ℓI<) -> Pred (List I D) _
  Sorted (_ , I) (s , f) = LinearOrderʰᵉ (snd (fst (I s))) useⁱ f

module _ where
  SortedList : {ℓS ℓI ℓI< : Level} -> (I : Indices ℓS ℓI ℓI<) ->
               {ℓD ℓD< : Level} (D : Type ℓD) {{LO : LinearOrderStr D ℓD<}} ->
               Type _
  SortedList I D = Σ (List I D) (Sorted I)


module _ {ℓS ℓI ℓI< : Level} (Idxs : Indices ℓS ℓI ℓI<) where
  private
    S : Type ℓS
    S = fst Idxs
    I' : S -> LOSet ℓI ℓI<
    I' s = fst (snd Idxs s)
    I : S -> Type ℓI
    I s = ⟨ I' s ⟩
    instance
      LO-I : {s : S} -> LinearOrderStr (I s) ℓI<
      LO-I {s} = snd (fst (snd Idxs s))
      DLO-I : {s : S} -> DecidableLinearOrderStr (LO-I {s})
      DLO-I {s} = snd (snd Idxs s)

  module _ {ℓD ℓD< : Level} {D : Type ℓD} {{LO : LinearOrderStr D ℓD<}}  where
    private

      SubSequenceIndexes : Rel (List Idxs D) _
      SubSequenceIndexes (s1 , f1) (s2 , f2) =
        ∀ (x : I s1) -> Σ[ y ∈ I s2 ] f1 x == f2 y

      isProp-Sorted-SubSequenceIndexes : (s1 s2 : SortedList Idxs D) ->
                                         isProp (SubSequenceIndexes ⟨ s1 ⟩ ⟨ s2 ⟩)
      isProp-Sorted-SubSequenceIndexes ((n1 , f1) , s1) ((n2 , f2) , s2) r1 r2 = funExt r3
        where
        r3 : ∀ (i : I n1) -> r1 i == r2 i
        r3 i =
          ΣProp-path (isSet-LinearlyOrdered D _ _)
            (connected-< (\i1<i2 -> irrefl-path-< (sym (snd (r1 i)) >=> (snd (r2 i)))
                                                  (s2.preserves-< i1<i2))
                         (\i2<i1 -> irrefl-path-< (sym (snd (r2 i)) >=> (snd (r1 i)))
                                                  (s2.preserves-< i2<i1)))
          where
          module s2 = LinearOrderʰ s2

      SubSequence≃Indexes : (s1 s2 : SortedList Idxs D) ->
                            SubSequence Idxs ⟨ s1 ⟩ ⟨ s2 ⟩ ≃ SubSequenceIndexes ⟨ s1 ⟩ ⟨ s2 ⟩
      SubSequence≃Indexes sl1@(l1@(n1 , f1) , s1) sl2@(l2@(n2 , f2) , s2) =
        isoToEquiv (isProp->iso (unsquash isProp-SSSI ∘ ∥-map forward) backward
                                squash isProp-SSSI)
        where
        module s1 = LinearOrderʰ s1
        module s2 = LinearOrderʰ s2

        isProp-SSSI = (isProp-Sorted-SubSequenceIndexes sl1 sl2)
        forward : Σ[ g ∈ (I n1 -> I n2) ] (LinearOrderʰ g × ∀ i -> (f1 i) == (f2 (g i))) ->
                  SubSequenceIndexes l1 l2
        forward (g , (_ , p)) = \i -> g i , p i
        backward : SubSequenceIndexes l1 l2 -> SubSequence Idxs l1 l2
        backward g = ∣ g' , gʰ , (\i -> snd (g i)) ∣
          where
          g' : I n1 -> I n2
          g' i = fst (g i)
          gʰ : LinearOrderʰ g'
          gʰ .LinearOrderʰ.preserves-< {i} {j} i<j =
            s2.reflects-< (subst2 _<_ p1 p2 (s1.preserves-< i<j))
            where
            p1 : f1 i == f2 (g' i)
            p1 = snd (g i)
            p2 : f1 j == f2 (g' j)
            p2 = snd (g j)

    record Sorted≼ (s1 s2 : SortedList Idxs D) : Type (ℓ-max ℓI ℓD) where
      private
        l1 = ⟨ s1 ⟩
        l2 = ⟨ s2 ⟩

      field
        indexes : SubSequenceIndexes l1 l2

      subsequence : SubSequence Idxs l1 l2
      subsequence = eqInv (SubSequence≃Indexes s1 s2) indexes

      preserves-∈ : {d : D} -> d l∈ l1 -> d l∈ l2
      preserves-∈ =
        ∥-map (\ (i , p) -> fst (indexes i) , sym (snd (indexes i)) >=> p)

    private
      refl-Sorted≼ : {s1 : SortedList Idxs D} -> Sorted≼ s1 s1
      refl-Sorted≼ .Sorted≼.indexes i = i , refl

      trans-Sorted≼ : {s1 s2 s3 : SortedList Idxs D} -> Sorted≼ s1 s2 -> Sorted≼ s2 s3 -> Sorted≼ s1 s3
      trans-Sorted≼ r12 r23 .Sorted≼.indexes i1 = ⟨ Σi3 ⟩ , snd Σi2 >=> snd Σi3
        where
        Σi2 = Sorted≼.indexes r12 i1
        Σi3 = Sorted≼.indexes r23 ⟨ Σi2 ⟩

      module _ {s1 s2 : SortedList Idxs D} where
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
          isProp-index : (x : I n1) -> isProp (Σ[ y ∈ I n2 ] f1 x == f2 y)
          isProp-index x (y1 , p1) (y2 , p2) =
            ΣProp-path (isSet-LinearlyOrdered D _ _) (LinearOrderʰᵉ.injective (snd s2) (sym p1 >=> p2))


    module _ (antisym-Sorted≼ : {s1 s2 : SortedList Idxs D} ->
                                Sorted≼ s1 s2 -> Sorted≼ s2 s1 -> s1 == s2) where
      PartialOrderStr-SortedList : PartialOrderStr (SortedList Idxs D) _
      PartialOrderStr-SortedList = record
        { _≤_ = Sorted≼
        ; isPartialOrder-≤ = record
          { isProp-≤ = isProp-Sorted≼
          ; refl-≤ = refl-Sorted≼
          ; trans-≤ = trans-Sorted≼
          ; antisym-≤ = antisym-Sorted≼
          }
        }
