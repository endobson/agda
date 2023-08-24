{-# OPTIONS --cubical --safe --exact-split #-}

module finset.choice where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import functions
open import truncation

private
  FinT-choice : {ℓA ℓP : Level} (n : Nat) (A : FinT n -> Type ℓA)
                (P : (i : FinT n) -> A i -> Type ℓP) ->
                ((i : FinT n) -> ∥ Σ (A i) (P i) ∥) ->
                ∥ (Σ[ f ∈ ((i : FinT n) -> A i) ] (∀ i -> P i (f i))) ∥
  FinT-choice zero    A P f = ∣ (\()) , (\()) ∣
  FinT-choice (suc n) A P f =
    ∥-map2 handle (f (inj-l tt)) (FinT-choice n (A ∘ inj-r) (P ∘ inj-r) (f ∘ inj-r))
    where
    handle : Σ (A (inj-l tt)) (P (inj-l tt)) ->
             (Σ[ g ∈ ((i : FinT n) -> A (inj-r i)) ] (∀ i -> P (inj-r i) (g i))) ->
             (Σ[ g ∈ ((i : FinT (suc n)) -> A i) ] (∀ i -> P i (g i)))
    handle (al , pl) (g , gp) = g' , gp'
      where
      g' : (i : FinT (suc n)) -> A i
      g' (inj-l tt) = al
      g' (inj-r i) = g i

      gp' : (i : FinT (suc n)) -> P i (g' i)
      gp' (inj-l tt) = pl
      gp' (inj-r i) = gp i

  Fin-choice : {ℓA ℓP : Level} (n : Nat) (A : Fin n -> Type ℓA)
               (P : (i : Fin n) -> A i -> Type ℓP) ->
               ((i : Fin n) -> ∥ Σ (A i) (P i) ∥) ->
               ∥ (Σ[ f ∈ ((i : Fin n) -> A i) ] (∀ i -> P i (f i))) ∥
  Fin-choice {ℓA} {ℓP} n =
    subst (\F -> (A : F -> Type ℓA)
                 (P : (i : F) -> A i -> Type ℓP) ->
                 ((i : F) -> ∥ Σ (A i) (P i) ∥) ->
                 ∥ (Σ[ f ∈ ((i : F) -> A i) ] (∀ i -> P i (f i))) ∥)
          (FinT=Fin n) (FinT-choice n)

abstract
  finite-choice : {ℓ₁ ℓ₂ ℓ₃ : Level} (A : FinSet ℓ₁) {B : ⟨ A ⟩ -> Type ℓ₂}
                  {P : (a : ⟨ A ⟩) -> B a -> Type ℓ₃} ->
                  (∀ (a : ⟨ A ⟩) -> ∃[ b ∈ B a ] (P a b)) ->
                  ∃[ f ∈ ((a : ⟨ A ⟩) -> B a) ] (∀ a -> P a (f a))
  finite-choice {ℓ₁} {ℓ₂} {ℓ₃} FA@(A , fsA) {B} {P} ps = ∥-bind handle fsA
    where
    Ans : Type (ℓ-max* 3 ℓ₁ ℓ₂ ℓ₃)
    Ans = Σ[ f ∈ ((a : A) -> B a) ] (∀ a -> P a (f a))
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> ∥ Ans ∥
    handle (nA , eqA) = ∥-map handle2 (Fin-choice nA _ _ (\i -> ps (eqInv eqA i)))
      where
      handle2 : (Σ[ f ∈ ((i : Fin nA) -> B (eqInv eqA i)) ]
                  (∀ i -> P (eqInv eqA i) (f i))) ->
                Ans
      handle2 (f , fp) = f' , fp'
        where
        f' : (a : A) -> B a
        f' a = substᵉ B (eqRet eqA a) (f (eqFun eqA a))
        fp' : (a : A) -> P a (f' a)
        fp' a = transport (\ i -> (P (eqRet eqA a i) (dep-path i))) (fp (eqFun eqA a))
          where
          dep-path : PathP (\i -> B (eqRet eqA a i)) (f (eqFun eqA a)) (f' a)
          dep-path = subst-filler B (eqRet eqA a) (f (eqFun eqA a))
