{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

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
open import finset.instances.sigma
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

module _ {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep = finMergeDep CM

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum = enumerationMerge CM

  equivSum : {n : Nat} -> (A ≃ Fin n) -> (A -> D) -> D
  equivSum = equivMerge CM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteSum : (I -> D) -> D
    finiteSum = finiteMerge CM

  finiteSumᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
  finiteSumᵉ (_ , f) = finiteMerge CM {{FI = record {isFin = f} }}

  abstract
    finiteSumᵉ-eval : {ℓ : Level} (A : FinSet ℓ) {n : Nat}
                      -> (eq : (⟨ A ⟩ ≃ Fin n)) -> (f : ⟨ A ⟩ -> D)
                      -> finiteSumᵉ A f == equivSum eq f
    finiteSumᵉ-eval = finiteMergeᵉ-eval CM

    finiteSumᵉ-convert : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                         (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D)
                         -> finiteSumᵉ A f == finiteSumᵉ B (f ∘ (eqFun eq))
    finiteSumᵉ-convert = finiteMergeᵉ-convert CM

    finiteSumᵉ-convert-iso : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                             (i : Iso ⟨ B ⟩ ⟨ A ⟩) (f : ⟨ A ⟩ -> D)
                             -> finiteSumᵉ A f == finiteSumᵉ B (f ∘ (Iso.fun i))
    finiteSumᵉ-convert-iso = finiteMergeᵉ-convert-iso CM


private
  module _ {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
    i<nSum : (n : Nat) -> (f : Nat -> D) -> D
    i<nSum n f = finSumDep n (\ (x , _) -> f x)


  i<nSum-zero : {n : Nat} -> i<nSum n (\i -> 0) == 0
  i<nSum-zero {n = zero}  = refl
  i<nSum-zero {n = suc n} = i<nSum-zero {n}

  i<nSum-one : {n : Nat} -> i<nSum n (\i -> 1) == n
  i<nSum-one {n = zero}  = refl
  i<nSum-one {n = suc n} = cong suc (i<nSum-one {n})

finiteSum-one : (n : Nat) -> finiteSum (\ (i : Fin n)  -> 1) == n
finiteSum-one n = finiteSumᵉ-eval _ (idEquiv _) (\i -> 1) >=> i<nSum-one {n}


cardinality-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
                (finA : isFinSet A) (finB : isFinSet B) ->
                cardinality ((A ⊎ B) , isFinSet-⊎ finA finB) ==
                cardinality (A , finA) +' cardinality (B , finB)
cardinality-⊎ finA finB =
  cardinality-path (_ , (isFinSet-⊎ finA finB))
                   (isFinSetΣ-⊎ (isFinSet->isFinSetΣ finA)
                                (isFinSet->isFinSetΣ finB))

cardinalityΣ-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                  cardinalityΣ ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSetΣ-Σ' B) ==
                  finSumDep n (\i -> cardinality (B i))
cardinalityΣ-Σ' {n = zero} FB = refl
cardinalityΣ-Σ' {n = suc n} FB = cong (cardinality (FB zero-fin) +'_) rec
  where
  rec : cardinalityΣ ((Σ[ i ∈ Fin n ] ⟨ FB (suc-fin i) ⟩) , isFinSetΣ-Σ' (FB ∘ suc-fin)) ==
        finSumDep n (\i -> cardinality (FB (suc-fin i)))
  rec = cardinalityΣ-Σ' (FB ∘ suc-fin)

cardinality-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                 cardinality ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) ==
                 finSumDep n (\i -> cardinality (B i))
cardinality-Σ' {n = n} B =
  cardinality-path ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) (isFinSetΣ-Σ' B)
  >=> cardinalityΣ-Σ' B


cardinality-Σ2 : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                 cardinality ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) ==
                 (finiteSum (\i -> cardinality (B i)))
cardinality-Σ2 B =
  cardinality-Σ' B >=> sym (finiteSumᵉ-eval (FinSet-Fin _) (idEquiv _) (\i -> cardinality (B i)))


-- TODO Make this work with different levels
cardinality-Σ3 : {ℓ : Level} (S : FinSet ℓ) (B : ⟨ S ⟩ -> FinSet ℓ) ->
                 cardinality (FinSet-Σ S B) == finiteSumᵉ S (\s -> cardinality (B s))
cardinality-Σ3 {ℓ} S@(S' , fin) B = unsquash (isSetNat _ _) (∥-map handle fin)
  where
  handle : (Σ[ n ∈ Nat ] (S' ≃ Fin n)) ->
           cardinality (FinSet-Σ S B) == finiteSumᵉ S (\s -> cardinality (B s))
  handle (n , eq) = sym path4 >=> path1 >=> path2
    where
    eq' = equiv⁻¹ eq
    B' : Fin n -> FinSet ℓ
    B' i = B (eqFun eq' i)
    BSet : S' -> Type ℓ
    BSet = fst ∘ B

    path1 : cardinality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
            (finiteSum (\i -> cardinality (B' i)))
    path1 = cardinality-Σ2 B'

    path2 : (finiteSum (\i -> cardinality (B' i))) ==
            (finiteSumᵉ S (\s -> cardinality (B s)))
    path2 = sym (finiteSumᵉ-convert S (FinSet-Fin n) eq' (\s -> cardinality (B s)))

    path3 : ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') == (FinSet-Σ S B)
    path3 = (ΣProp-path isProp-isFinSet (sym (ua (reindexΣ eq' BSet))))

    path4 : cardinality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
            cardinality (FinSet-Σ S B)
    path4 = cong cardinality path3

finiteSum'-one : {ℓ : Level} {S : FinSet ℓ} -> finiteSumᵉ S (\s -> 1) == cardinality S
finiteSum'-one {S = S@(S' , FS)} = unsquash (isSetNat _ _) (∥-map handle FS)
  where
  handle : Σ[ n ∈ Nat ] (S' ≃ Fin n) -> finiteSumᵉ S (\s -> 1) == cardinality S
  handle (n , eq) = finiteSumᵉ-convert S (FinSet-Fin n) (equiv⁻¹ eq) (\_ -> 1) >=>
                    finiteSum-one n >=> sym (cardinality-path S (n , ∣ eq ∣))


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM
    module S = Semiring S

  abstract
    finiteSum-Bot : (f : Bot -> D) -> finiteSum f == 0#
    finiteSum-Bot f = finiteSumᵉ-eval FinSet-Bot (equiv⁻¹ Fin-Bot-eq) f

  finiteSum-Fin0 : (f : (Fin 0) -> D) -> finiteSum f == 0#
  finiteSum-Fin0 f = finiteSumᵉ-eval (FinSet-Fin 0) (idEquiv _) f
