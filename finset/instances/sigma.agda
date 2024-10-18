{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.sigma where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finset
open import finset.instances
open import finset.instances.base
open import finset.instances.sum
open import functions
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.nat
open import semiring
open import sigma
open import sigma.base
open import sum
open import truncation
open import univalence

private
  variable
    ℓ : Level
    A : Type ℓ

opaque
  ΣFin-suc-eq' : (n : Nat) (P : (Fin (suc n)) -> Type ℓ) ->
                 (Σ[ i ∈ Fin (suc n) ] (P i)) ≃ (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i)))
  ΣFin-suc-eq' n P = (isoToEquiv i)
    where
    module _ where
      forward : (Σ[ i ∈ Fin (suc n) ] (P i)) -> (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i)))
      forward ((0 , lt) , p) = inj-l (substᵉ P (fin-i-path refl) p)
      forward ((suc i , lt) , p) = inj-r ((i , pred-≤ lt) , (substᵉ P (fin-i-path refl) p))

      backward : (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i))) -> (Σ[ i ∈ Fin (suc n) ] (P i))
      backward (inj-l p) = (zero-fin , p)
      backward (inj-r (i , p)) = (suc-fin i , p)

      module _ (i : Fin n) (p : (P (suc-fin i))) where
        fst-path : fst (proj-r (forward (backward (inj-r (i , p)))) tt) == i
        fst-path = fin-i-path refl

        x : Fin (suc n)
        x = suc-fin i
        y : Fin (suc n)
        y = suc-fin (fst-path i0)
        p1 p2 : x == y
        p1 = sym (cong suc-fin fst-path)
        p2 = (fin-i-path refl)

        fb-r-snd : PathP (\k -> P (p1 (~ k))) (substᵉ P p2 p) p
        fb-r-snd = symP (subst-filler2 P p1 p2 (isSetFin x y p1 p2) p)

        fb-r : forward (backward (inj-r (i , p))) == inj-r (i , p)
        fb-r k = inj-r (fst-path k , fb-r-snd k)

      module _ (p : (P zero-fin)) where
        fb-l : forward (backward (inj-l p)) == inj-l p
        fb-l = cong inj-l path
          where
          path-i : zero-fin == zero-fin
          path-i = fin-i-path refl

          path : (substᵉ P path-i p) == p
          path = sym (subst-filler2 P refl path-i (isSetFin _ _ _ _) p)

      bf-zero : (lt : 0 < (suc n)) (p : P (0 , lt)) ->
                backward (forward ((0 , lt) , p)) == ((0 , lt) , p)
      bf-zero lt p = (\i -> path1 (~ i) , path2 (~ i))
        where
        path1 : (0 , lt) == zero-fin
        path1 = fin-i-path refl
        path2 : PathP (\i -> P (path1 i)) p (substᵉ P path1 p)
        path2 = subst-filler P path1 p

      bf-suc : (i : Nat) (lt : (suc i) < (suc n)) (p : P (suc i , lt)) ->
                backward (forward ((suc i , lt) , p)) == ((suc i , lt) , p)
      bf-suc i lt p = (\i -> path1 (~ i) , path2 (~ i))
        where
        path1 : (suc i , lt) == (suc i , _)
        path1 = fin-i-path refl
        path2 : PathP (\i -> P (path1 i)) p (substᵉ P path1 p)
        path2 = subst-filler P path1 p


    open Iso
    i : Iso (Σ[ i ∈ Fin (suc n) ] (P i)) (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i)))
    i .fun = forward
    i .inv = backward
    i .rightInv (inj-l p) = fb-l p
    i .rightInv (inj-r (i , p)) = fb-r i p
    i .leftInv ((0 , lt) , p) = bf-zero lt p
    i .leftInv ((suc i , lt) , p) = bf-suc i lt p


isFinSetΣ-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) -> isFinSetΣ (Σ[ i ∈ Fin n ] ⟨ B i ⟩)
isFinSetΣ-Σ' {ℓ} {zero} FB = 0 , ∣ isoToEquiv i ∣
  where
  B : Fin 0 -> Type ℓ
  B = fst ∘ FB
  open Iso
  i : Iso (Σ[ i ∈ Fin 0 ] (B i)) (Fin 0)
  i .fun (i , _) = bot-elim (¬fin-zero i)
  i .inv i = bot-elim (¬fin-zero i)
  i .rightInv i = bot-elim (¬fin-zero i)
  i .leftInv (i , _) = bot-elim (¬fin-zero i)
isFinSetΣ-Σ' {ℓ} {suc n} FB = substᵉ isFinSetΣ (sym (ua (ΣFin-suc-eq' n B))) combined
  where
  B : Fin (suc n) -> Type ℓ
  B = fst ∘ FB
  isFinSetΣB : (s : Fin (suc n)) -> isFinSetΣ (B s)
  isFinSetΣB s = isFinSet->isFinSetΣ (snd (FB s))

  rec : isFinSetΣ (Σ[ i ∈ Fin n ] (B (suc-fin i)))
  rec = isFinSetΣ-Σ' (FB ∘ suc-fin)

  zero-case : isFinSetΣ (B zero-fin)
  zero-case = isFinSetΣB zero-fin

  combined : isFinSetΣ (B zero-fin ⊎ (Σ[ i ∈ Fin n ] (B (suc-fin i))))
  combined = isFinSetΣ-⊎ zero-case rec

opaque
  isFinSet-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) -> isFinSet (Σ[ i ∈ Fin n ] ⟨ B i ⟩)
  isFinSet-Σ' B = isFinSetΣ->isFinSet (isFinSetΣ-Σ' B)

  isFinSet-Σ : {ℓ₁ ℓ₂ : Level} (S : FinSet ℓ₁) (B : ⟨ S ⟩ -> FinSet ℓ₂) ->
               isFinSet (Σ[ s ∈ ⟨ S ⟩ ] ⟨ B s ⟩)
  isFinSet-Σ {ℓ₁} {ℓ₂} (S , n-eq) FB = unsquash isProp-isFinSet (∥-map handle n-eq)
    where
    handle : Σ[ n ∈ Nat ] (S ≃ Fin n) -> isFinSet (Σ[ s ∈ S ] ⟨ FB s ⟩)
    handle (n , eq) = isFinSet-equiv (equiv⁻¹ eqΣ) inner
      where
      eq' : Fin n ≃ S
      eq' = equiv⁻¹ eq
      inner : isFinSet (Σ[ i ∈ Fin n ] (fst (FB (eqFun eq' i))))
      inner = isFinSet-Σ' (\i -> (FB (eqFun eq' i)))
      eqΣ : (Σ[ s ∈ S ] ⟨ FB s ⟩) ≃ (Σ[ i ∈ Fin n ] (fst (FB (eqFun eq' i))))
      eqΣ = reindexΣ eq' (\s -> ⟨ FB s ⟩)

FinSet-Σ : {ℓ₁ ℓ₂ : Level} (S : FinSet ℓ₁) (B : ⟨ S ⟩ -> FinSet ℓ₂) -> FinSet _
FinSet-Σ S B = (Σ[ s ∈ ⟨ S ⟩ ] ⟨ B s ⟩) , isFinSet-Σ S B

FinSet-× : {ℓ₁ ℓ₂ : Level} (A : FinSet ℓ₁) (B : FinSet ℓ₂) -> FinSet _
FinSet-× A B = FinSet-Σ A (\_ -> B)

FinSetStr-Σ : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (B : A -> Type ℓ₂) {{FA : FinSetStr A}}
              {{FB : {a : A} -> FinSetStr (B a)}} -> FinSetStr (Σ A B)
FinSetStr-Σ A B {{FA = FA}} {{FB = FB}} = record
  { isFin = isFinSet-Σ (_ , FinSetStr.isFin FA) (\a -> B a , FinSetStr.isFin (FB {a}))
  }

instance
  FinSetStr-× : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> {{FinSetStr A}} -> {{FinSetStr B}} ->
    FinSetStr (A × B)
  FinSetStr-× {A = A} {B = B} = FinSetStr-Σ A (\_ -> B)
