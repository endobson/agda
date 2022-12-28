{-# OPTIONS --cubical --safe --exact-split #-}

module non-empty-finset where

open import base
open import sum
open import cubical
open import equivalence
open import fin
open import hlevel
open import fin-algebra
open import finset
open import finsum
open import isomorphism
open import nat hiding (_<_)
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import relation
open import sigma.base
open import truncation
open import univalence


isNonEmptyFinSet : {ℓ : Level} -> Pred (FinSetΣ ℓ) ℓ-zero
isNonEmptyFinSet fs = 0 < cardinalityΣ fs

NonEmptyFinSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
NonEmptyFinSet ℓ = Σ (FinSetΣ ℓ) isNonEmptyFinSet

isSingletonFinSet : {ℓ : Level} -> Pred (FinSetΣ ℓ) ℓ-zero
isSingletonFinSet fs = cardinalityΣ fs == 1

module _ {ℓ : Level} where
  NonEmptyFinSet-Topℓ : NonEmptyFinSet ℓ 
  NonEmptyFinSet-Topℓ =
    (Lift ℓ Top , (1 , ∣ liftEquiv _ _ >eq> (equiv⁻¹ Fin-Top-eq) ∣)) , zero-<

  NonEmptyFinSet-Finℓ : (n : Nat) -> NonEmptyFinSet ℓ 
  NonEmptyFinSet-Finℓ n =
    (Lift ℓ (Fin (suc n)) , (suc n , ∣ (liftEquiv _ _) ∣)) , zero-<


  NonEmptyFinSet-⊎ : NonEmptyFinSet ℓ -> NonEmptyFinSet ℓ -> NonEmptyFinSet ℓ
  NonEmptyFinSet-⊎ ((t1 , fs1) , 0<c1) ((t2 , fs2) , 0<c2) = 
    ((t1 ⊎ t2) , isFinSetΣ-⊎ fs1 fs2) , (+-preserves-0< 0<c1 0<c2)

  split-NonEmptyFinSet : 
    (fs : NonEmptyFinSet ℓ) ->
    isSingletonFinSet (fst fs) ⊎ 
    (∥ (Σ[ fs1 ∈ NonEmptyFinSet ℓ ] (Σ[ fs2 ∈ NonEmptyFinSet ℓ ] 
         (fs == NonEmptyFinSet-⊎ fs1 fs2) )) ∥)
  split-NonEmptyFinSet ((T , (0 , eq)) , 0<c) = bot-elim (irrefl-< 0<c)
  split-NonEmptyFinSet ((T , (1 , eq)) , _) = inj-l refl
  split-NonEmptyFinSet fs@((T , ((suc (suc n)) , eq)) , _) = 
    inj-r (∥-map handle eq)
    where
    handle : T ≃ Fin (suc (suc n)) -> 
             (Σ[ fs1 ∈ NonEmptyFinSet ℓ ] (Σ[ fs2 ∈ NonEmptyFinSet ℓ ] 
               (fs == NonEmptyFinSet-⊎ fs1 fs2) ))
    handle eq = 
      NonEmptyFinSet-Topℓ ,
      NonEmptyFinSet-Finℓ n , 
      (ΣProp-path isProp-< (ΣProp-path isProp-isFinSetΣ (ua eq')))
      where
      eq' : T ≃ (Lift ℓ Top ⊎ Lift ℓ (Fin (suc n)))
      eq' = eq >eq> Fin-suc-⊎-eq (suc n) >eq> 
            (⊎-equiv (equiv⁻¹ (liftEquiv _ _)) (equiv⁻¹ (liftEquiv _ _)))

  --module _ {ℓP : Level} {P : Pred (NonEmptyFinSet ℓ) ℓP} where
  --  NonEmptyFinSet-elimProp :
  --    (isPropP : ∀ fs -> isProp (P fs)) ->
  --    (∀ fs -> isSingletonFinSet (fst fs) -> P fs) ->
  --    (∀ fs fs1 fs2 -> P fs1 -> P fs2 -> (fs == NonEmptyFinSet-⊎ fs1 fs2) -> P fs) ->
  --    (fs : NonEmptyFinSet ℓ) -> P fs
  --  NonEmptyFinSet-elimProp prop single-case branch-case fs@((T , (n , eq)) , 0<n) = (handle n 0<n T eq)
  --    where
  --    handle : (n : Nat) (0<n : 0 < n) (T : Type ℓ) (eq : ∥ T ≃ Fin n ∥) -> P ((T , (n , eq)) , 0<n)
  --    handle 0 0<0 = bot-elim (irrefl-< 0<0)
  --    handle 1 0<1 T eq = single-case ((T , (1 , eq)) , 0<1) refl
  --    handle (suc (suc n)) 0<ssn T ∣eq∣ = unsquash (prop _) (∥-map handle2 ∣eq∣)
  --      where
  --      handle2 : T ≃ Fin (suc (suc n)) -> P ((T , ((suc (suc n)) , ∣eq∣)) , 0<ssn)
  --      handle2 eq = 
  --        branch-case _ 
  --          NonEmptyFinSet-Topℓ (NonEmptyFinSet-Finℓ n)
  --          (handle _ _ _ _) (handle _ _ _ _)
  --          (ΣProp-path isProp-< (ΣProp-path isProp-isFinSetΣ (ua eq')))
  --        where
  --        eq' : T ≃ (Lift ℓ Top ⊎ Lift ℓ (Fin (suc n)))
  --        eq' = eq >eq> Fin-suc-⊎-eq (suc n) >eq> 
  --              (⊎-equiv (equiv⁻¹ (liftEquiv _ _)) (equiv⁻¹ (liftEquiv _ _)))
