{-# OPTIONS --cubical --safe --exact-split #-}

module fin.without-point where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import functions
open import hlevel
open import isomorphism
open import nat
open import sigma.base
open import sum
open import without-point

private
  avoid : (n : Nat) -> (i : FinT (suc n)) -> FinT n -> WithoutPoint (FinT (suc n)) i
  avoid (suc n) (inj-l tt) j = inj-r j , inj-l!=inj-r ∘ sym
  avoid (suc n) (inj-r i) (inj-l tt) = (inj-l tt) , inj-l!=inj-r
  avoid (suc n) (inj-r i) (inj-r j) =
    case (avoid n i j) of (\{ (i , p) -> (inj-r i) , p ∘ inj-r-injective})

  remove : (n : Nat) -> (i : FinT (suc n)) -> (WithoutPoint (FinT (suc n)) i) -> FinT n
  remove _       (inj-l tt) (inj-l tt , i!=j) = bot-elim (i!=j refl)
  remove (suc n) (inj-l tt) (inj-r j  , i!=j) = j
  remove (suc n) (inj-r i)  (inj-l tt , i!=j) = (inj-l tt)
  remove (suc n) (inj-r i)  (inj-r j  , i!=j) =
    inj-r (remove n i (j , i!=j ∘ cong inj-r))

  avoid-remove : (n : Nat) (b : FinT (suc n)) (i : WithoutPoint (FinT (suc n)) b) ->
                 avoid n b (remove n b i) == i
  avoid-remove _ (inj-l tt) (inj-l tt , p) = bot-elim (p refl)
  avoid-remove (suc n) (inj-l tt) (inj-r j , _) = ΣProp-path (isProp¬ _) refl
  avoid-remove (suc n) (inj-r i)  (inj-l tt , _) = ΣProp-path (isProp¬ _) refl
  avoid-remove (suc n) (inj-r i) (inj-r j , _) =
    ΣProp-path (isProp¬ _) (cong (inj-r ∘ fst) (avoid-remove n i (j , _)))

  remove-avoid : (n : Nat) (b : FinT (suc n)) (i : FinT n) ->
                 remove n b (avoid n b i) == i
  remove-avoid (suc n) (inj-l tt) (inj-l tt) = refl
  remove-avoid (suc n) (inj-l tt) (inj-r j)  = refl
  remove-avoid (suc n) (inj-r i)  (inj-l tt) = refl
  remove-avoid (suc n) (inj-r i) (inj-r j) =
    cong inj-r (cong (remove n i) (ΣProp-path (isProp¬ _) refl) >=>
                remove-avoid n i j)

  RA-eq' : {n : Nat} -> (a : FinT (suc n)) -> (WithoutPoint (FinT (suc n)) a) ≃ FinT n
  RA-eq' {n} a = isoToEquiv (iso (remove n a) (avoid n a) (remove-avoid n a) (avoid-remove n a))

WithoutPoint-Fin-eq : {n : Nat} -> (a : Fin n) -> (WithoutPoint (Fin n) a) ≃ Fin (pred n)
WithoutPoint-Fin-eq {zero} a = bot-elim (¬fin-zero a)
WithoutPoint-Fin-eq {suc n} =
  subst2 (\F Fp -> ∀ (a : F) -> WithoutPoint F a ≃ Fp) (FinT=Fin (suc n)) (FinT=Fin n) (RA-eq' {n})
