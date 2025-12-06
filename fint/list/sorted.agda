{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module fint.list.sorted where

open import base
open import equality
open import equivalence
open import fint.list
open import fin-algebra
open import hlevel.base
open import hlevel.order
open import hlevel.sum
open import order
open import order.homomorphism
open import order.instances.fint
open import relation
open import sigma.base
open import truncation
open import type-algebra

private
  variable
    ℓ ℓ< : Level
    A : Type ℓ

Sorted : {ℓ ℓ< : Level} {A : Type ℓ} {A< : Rel A ℓ<} -> {{LO : isLinearOrder A<}} -> Pred (FinList A) _
Sorted (n , f) = LinearOrderʰ f

SortedList : {ℓ ℓ< : Level} (A : Type ℓ) {A< : Rel A ℓ<} -> {{LO : isLinearOrder A<}} -> Type _
SortedList A = Σ (FinList A) Sorted

module _ {ℓB ℓB< : Level} {B : Type ℓB} {B< : Rel B ℓB<} {{LO : isLinearOrder B<}} where
  _sl∈_ : REL B (SortedList B) ℓB
  b sl∈ (l , s) = b l∈ l

  _sl∈'_ : REL B (SortedList B) ℓB
  b sl∈' (l , s) = b l∈' l

module _ {ℓA ℓ< : Level} {A : Type ℓA} {A< : Rel A ℓ<} {{LO : isLinearOrder A<}} where

  LowerBound< : FinList A -> Pred A _
  LowerBound< l a = {a2 : A} -> a2 l∈ l -> a < a2

  sortedlist-empty : SortedList A
  sortedlist-empty = finlist-empty , s
    where
    s : Sorted finlist-empty
    s .LinearOrderʰ.preserves-< ()

  sortedlist-cons : (a : A) -> (l : SortedList A) -> LowerBound< ⟨ l ⟩ a -> SortedList A
  sortedlist-cons a (l@(n , f) , s) lb = l' , s'
    where
    l' : FinList A
    l' = finlist-cons a l
    s' : Sorted l'
    s' .LinearOrderʰ.preserves-< (finT<-lr) = lb ∣ _ , refl ∣
    s' .LinearOrderʰ.preserves-< (finT<-rr lt) = s .LinearOrderʰ.preserves-< lt


  abstract
    SortedList-Ind : {ℓP : Level} (P : Pred (SortedList A) ℓP) ->
                     (pE : P sortedlist-empty) ->
                     (pC : ∀ (a : A) -> (l : SortedList A) ->
                             (lb : LowerBound< ⟨ l ⟩ a) ->
                             (P l) -> P (sortedlist-cons a l lb)) ->
                     (l : SortedList A) -> P l
    SortedList-Ind {ℓP} P pE pC (l , s) =
      FinList-Ind P' p'E p'C l s
      where
      P' : FinList A -> Type (ℓ-max* 3 ℓA ℓ< ℓP)
      P' l = ∀ s -> P (l , s)

      p'E : P' finlist-empty
      p'E s = subst P (ΣProp-path isProp-LinearOrderʰ refl) pE

      p'C : (a : A) -> (l : FinList A) -> (P' l) -> P' (finlist-cons a l)
      p'C a l@(n , f) p'-l s-al =
        subst P (ΣProp-path isProp-LinearOrderʰ refl) (pC a (l , sl) lb (p'-l sl))
        where
        sl : Sorted l
        sl .LinearOrderʰ.preserves-< i<j =
           (s-al .LinearOrderʰ.preserves-< (finT<-rr i<j))

        lb : LowerBound< l a
        lb {a2} a2∈l = unsquash isProp-< (∥-map handle a2∈l)
          where
          handle : a2 l∈' l -> a < a2
          handle (_ , p) = trans-<-= (s-al .LinearOrderʰ.preserves-< finT<-lr) p

  isProp-sl∈' : (a : A) (l : SortedList A) -> isProp (a sl∈' l)
  isProp-sl∈' a (l , s) (i1 , p1) (i2 , p2) =
    ΣProp-path (isSet-LinearlyOrdered A _ _)
      (connected-< (\i1<i2 -> irrefl-path-< (p1 >=> sym p2) (s.preserves-< i1<i2))
                   (\i2<i1 -> irrefl-path-< (p2 >=> sym p1) (s.preserves-< i2<i1)))
    where
    module s = LinearOrderʰ s

  sl∈-eq-sl∈' : (a : A) (l : SortedList A) -> a sl∈ l ≃ a sl∈' l
  sl∈-eq-sl∈' a l = ∥-Prop-eq (isProp-sl∈' a l)


  sortedlist-cons-l∈-eq : (a : A) (l : SortedList A) (lb : LowerBound< ⟨ l ⟩ a) ->
                          (∀ a2 -> (a2 sl∈ (sortedlist-cons a l lb)) ≃
                                   (a2 sl∈ l ⊎ a2 == a))
  sortedlist-cons-l∈-eq a (l , s) lb a2 =
    finlist-cons-l∈-eq a l a2 >eq>
    ∥-Prop-eq (isProp⊎ squash (isSet-LinearlyOrdered A a2 a) f)
    where
    f : a2 l∈ l -> a2 == a -> Bot
    f a2∈l p = irrefl-path-< (sym p) (lb a2∈l)
