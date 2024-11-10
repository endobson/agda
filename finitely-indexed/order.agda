{-# OPTIONS --cubical --safe --exact-split #-}

module finitely-indexed.order where

open import base
open import equality
open import fin-algebra
open import finitely-indexed
open import finset
open import finset.order.base
open import hlevel
open import nat.order using (WellFounded-Nat<)
open import order
open import order.instances.nat
open import relation
open import truncation


Indexable< : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (B : Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Indexable< A B =
  (∀ n -> isIndexable B n -> ∃[ m ∈ Nat ] (m < n × isIndexable A m))

Indexable<' : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (B : Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Indexable<' A B =
  ∃[ n ∈ Nat ] (isIndexable A n × (∀ m -> (isIndexable B m) -> n < m))


KFinSet< : {ℓ₁ ℓ₂ : Level} -> (A : KFinSet⁻ ℓ₁) -> (B : KFinSet⁻ ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
KFinSet< (A , _) (B , _) = Indexable< A B

KFinSet<' : {ℓ₁ ℓ₂ : Level} -> (A : KFinSet⁻ ℓ₁) -> (B : KFinSet⁻ ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
KFinSet<' (A , _) (B , _) = Indexable<' A B

isProp-Indexable< : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (B : Type ℓ₂) -> isProp (Indexable< A B)
isProp-Indexable< _ _ = isPropΠ2 (\_ _ -> squash)

private
  Acc-Indexable< : {ℓ : Level} (A : Type ℓ) (n : Nat) ->
                   isIndexable A n -> Acc _<_ n -> Acc Indexable< A
  Acc-Indexable< {ℓ} B n idx-B (acc nat-f) = acc helper
    where
    helper : (A : Type ℓ) -> Indexable< A B -> Acc Indexable< A
    helper A f = unsquash (isProp-Acc Indexable< A) (∥-map handle (f n idx-B))
      where
      handle : Σ[ m ∈ Nat ] (m < n × isIndexable A m) -> Acc Indexable< A
      handle (m , m<n , idx-A) = Acc-Indexable< A m idx-A (nat-f m m<n)

  Acc-Indexable<' : {ℓ : Level} (A : Type ℓ) (n : Nat) ->
                   isIndexable A n -> Acc _<_ n -> Acc Indexable<' A
  Acc-Indexable<' {ℓ} B n idx-B (acc nat-f) = acc helper
    where
    helper : (A : Type ℓ) -> Indexable<' A B -> Acc Indexable<' A
    helper A A<B = unsquash (isProp-Acc Indexable<' A) (∥-map helper2 A<B)
      where
      helper2 : Σ[ m ∈ Nat ] (isIndexable A m × (∀ n -> (isIndexable B n) -> m < n)) ->
                Acc Indexable<' A
      helper2 (m , idx-A , f) = Acc-Indexable<' A m idx-A (nat-f m (f n idx-B))


  WellFounded-Indexable< : {ℓ : Level} {A : Type ℓ} -> isListable A -> Acc Indexable< A
  WellFounded-Indexable< {A = A} list-A =
    unsquash (isProp-Acc Indexable< A) (∥-map handle list-A)
    where
    handle : Σ[ n ∈ Nat ] (isIndexable A n) -> Acc Indexable< A
    handle (n , idx-A) = Acc-Indexable< A n idx-A (WellFounded-Nat< n)

  module _ {ℓA ℓAR ℓB ℓBR : Level} (A : Type ℓA) (B : Type ℓB)
           (f : A -> B)
           (RA : Rel A ℓAR) (RB : Rel B ℓBR)
           (RA->RB : ∀ a1 a2 -> RA a1 a2 -> RB (f a1) (f a2)) where
    AccRB->AccRA : ∀ a -> Acc RB (f a) -> Acc RA a
    AccRB->AccRA a1 (acc g) = acc (\a2 ra2a1 -> AccRB->AccRA a2 (g (f a2) (RA->RB a2 a1 ra2a1)))

WellFounded-KFinSet< : {ℓ : Level} -> WellFounded (KFinSet< {ℓ} {ℓ})
WellFounded-KFinSet< {ℓ} KA@(A , isKFin-A) =
  AccRB->AccRA (KFinSet⁻ ℓ) (Type ℓ) fst KFinSet< Indexable< (\a b r -> r) KA
               (WellFounded-Indexable< list-A)
  where
  list-A : isListable A
  list-A =
    ∥-map (\{ (n , f) -> n , ∣ subst (\F -> Σ (F -> A) isSurjective) (sym (FinT=Fin n)) f ∣}) isKFin-A
