{-# OPTIONS --cubical --safe --exact-split #-}

module finset.without-point where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import fin.without-point
open import fin-algebra
open import finset
open import finset.order.base
open import finset.cardinality
open import functions
open import hlevel
open import isomorphism
open import order
open import order.instances.nat
open import nat
open import sigma
open import sigma.base
open import sum
open import truncation
open import without-point


private
  variable
    ℓ : Level

private
  isFinSetΣ-WithoutPoint : {A : Type ℓ} -> isFinSetΣ A -> (a : A) -> isFinSetΣ (WithoutPoint A a)
  isFinSetΣ-WithoutPoint {A = A} (n , eq') a = pred n , ∥-map handle eq'
    where
    module _ (eq : A ≃ Fin n) where
      bad = (eqFun eq a)
      eq2 : WithoutPoint A a ≃ WithoutPoint (Fin n) bad
      eq2 = isoToEquiv (iso f g fg gf)
        where
        f : WithoutPoint A a -> WithoutPoint (Fin n) bad
        f (a2 , p) = eqFun eq a2 , (p ∘ (\p -> sym (eqRet eq a2) >=> p >=> eqRet eq a) ∘ cong (eqInv eq))

        g : WithoutPoint (Fin n) bad -> WithoutPoint A a
        g (i , p) = eqInv eq i , (p ∘ (\p -> sym (eqSec eq i) >=> p) ∘ cong (eqFun eq))

        fg : ∀ i -> f (g i) == i
        fg i = ΣProp-path (isProp¬ _) (eqSec eq (fst i))

        gf : ∀ a2 -> g (f a2) == a2
        gf a2 = ΣProp-path (isProp¬ _) (eqRet eq (fst a2))

      handle : WithoutPoint A a ≃ Fin (pred n)
      handle = (eq2 >eq> WithoutPoint-Fin-eq bad)

isFinSet-WithoutPoint : {A : Type ℓ} -> isFinSet A -> (a : A) -> isFinSet (WithoutPoint A a)
isFinSet-WithoutPoint {A = A} fsA a =
  isFinSetΣ->isFinSet (isFinSetΣ-WithoutPoint (isFinSet->isFinSetΣ fsA) a)

FinSet-WithoutPoint : (A : FinSet ℓ) (a : ⟨ A ⟩) -> FinSet ℓ
FinSet-WithoutPoint (A , fsA) a = WithoutPoint A a , isFinSet-WithoutPoint fsA a

FinSetStr-WithoutPoint : {A : Type ℓ} {{FA : FinSetStr A}} {a : A} -> FinSetStr (WithoutPoint A a)
FinSetStr-WithoutPoint = record { isFin = isFinSet-WithoutPoint isFinSetⁱ _ }

cardinality-WithoutPoint : (A : FinSet ℓ) -> (a : ⟨ A ⟩) ->
                           cardinality (FinSet-WithoutPoint A a) == pred (cardinality A)
cardinality-WithoutPoint FA@(A , fsA) a =
  cardinality-path (FinSet-WithoutPoint FA a)
                   (isFinSetΣ-WithoutPoint (isFinSet->isFinSetΣ fsA) a)

FinSet<-WithoutPoint : (A : FinSet ℓ) -> (a : ⟨ A ⟩) ->
                       FinSet< (FinSet-WithoutPoint A a) A
FinSet<-WithoutPoint A a = handle (cardinality A) refl
  where
  handle : (n : Nat) -> cardinality A == n -> FinSet< (FinSet-WithoutPoint A a) A
  handle zero    p = bot-elim (eqInv (uninhabited-cardinality0 A) p a)
  handle (suc n) p =
    path-≤ (cong suc (cardinality-WithoutPoint A a) >=> cong suc (cong pred p) >=> sym p)


