{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.cardinality where

open import additive-group
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid.instances
open import finset
open import finset.cardinality
open import finset.instances
open import finset.instances.sigma
open import finset.instances.sum
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import nat
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import sigma
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
  where
  private
    instance
      IACM = ACM

    finSumDep-one : {n : Nat} -> finSumDep n (\i -> 1) == n
    finSumDep-one {zero}  = refl
    finSumDep-one {suc n} = cong suc finSumDep-one

    finiteSumᵉ-one-ℕ : {ℓ : Level} (S : FinSet ℓ) -> finiteSumᵉ S (\s -> 1) == cardinality S
    finiteSumᵉ-one-ℕ S@(S' , FS) = unsquash (isSetNat _ _) (∥-map handle FS)
      where
      handle : Σ[ n ∈ Nat ] (S' ≃ Fin n) -> finiteSumᵉ S (\s -> 1) == cardinality S
      handle (n , eq) =
        finiteSumᵉ-eval S eq (\_ -> 1) >=>
        finSumDep-one >=>
        sym (cardinality-path S (n , ∣ eq ∣))

  opaque
    finiteSumᵉ-one : {ℓ : Level} (I : FinSet ℓ) ->
      Path D (finiteSumᵉ I (\i -> 1#)) (ℕ->Semiring (cardinality I))
    finiteSumᵉ-one FI@(I , isFin-I) =
      cong finiteSum (funExt (\(_ : I) -> (sym (Semiringʰ.preserves-1# h1)))) >=>
      finiteMerge-homo-inject h2 >=>
      cong ℕ->Semiring (finiteSumᵉ-one-ℕ FI)
      where
      instance
        IFI : FinSetStr I
        IFI = record { isFin = isFin-I }

      h1 : Semiringʰᵉ useⁱ S ℕ->Semiring
      h1 = ∃!-prop ∃!ℕ->Semiring

      h2 : CommMonoidʰᵉ (CommMonoid-+ ℕ) (CommMonoid-+ D) ℕ->Semiring
      h2 = record { monoidʰ = Semiringʰ.+ʰ h1 }

    finiteSum-one : {ℓ : Level} {I : Type ℓ} {{FI : FinSetStr I}} ->
      Path D (finiteSum (\(i : I) -> 1#)) (ℕ->Semiring (cardinalityⁱ I))
    finiteSum-one = finiteSumᵉ-one (_ , isFinSetⁱ)

    finiteSum-constant : {ℓ : Level} {I : Type ℓ} {{FI : FinSetStr I}} {k : D} ->
      (finiteSum (\(i : I) -> k)) == (ℕ->Semiring (cardinalityⁱ I)) * k
    finiteSum-constant =
      cong finiteSum (funExt (\_ -> (sym *-right-one))) >=>
      finiteSum-* >=>
      *-right finiteSum-one >=>
      *-commute

opaque
  cardinality-⊎ : {ℓA ℓB : Level}
    (A : FinSet ℓA) (B : FinSet ℓB) -> cardinality (FinSet-⊎ A B) == cardinality A + cardinality B
  cardinality-⊎ A@(_ , finA) B@(_ , finB) =
    cardinality-path (FinSet-⊎ A B)
                     (isFinSetΣ-⊎ (isFinSet->isFinSetΣ finA)
                                  (isFinSet->isFinSetΣ finB))

private
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

opaque
  cardinality-Σ : {ℓS ℓB : Level} (S : FinSet ℓS) (B : ⟨ S ⟩ -> FinSet ℓB) ->
                  cardinality (FinSet-Σ S B) == finiteSumᵉ S (\s -> cardinality (B s))
  cardinality-Σ {ℓS} {ℓB} S@(S' , fin) B = unsquash (isSetNat _ _) (∥-map handle fin)
    where
    handle : (Σ[ n ∈ Nat ] (S' ≃ Fin n)) ->
             cardinality (FinSet-Σ S B) == finiteSumᵉ S (\s -> cardinality (B s))
    handle (n , eq) = sym path3 >=> path1 >=> path2
      where
      eq' : Fin n ≃ S'
      eq' = equiv⁻¹ eq
      B' : Fin n -> FinSet ℓB
      B' i = B (eqFun eq' i)
      BSet : S' -> Type ℓB
      BSet = fst ∘ B

      path1 : cardinality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
              (finiteSum (\i -> cardinality (B' i)))
      path1 = cardinality-Σ2 B'

      path2 : (finiteSum (\i -> cardinality (B' i))) ==
              (finiteSumᵉ S (\s -> cardinality (B s)))
      path2 = sym (finiteSumᵉ-convert S (FinSet-Fin n) eq' (\s -> cardinality (B s)))

      path3 : cardinality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
              cardinality (FinSet-Σ S B)
      path3 =
        cardinality-≃-path ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') (FinSet-Σ S B)
          (equiv⁻¹ (reindexΣ eq' BSet))


  cardinality-× : {ℓ : Level} (S₁ S₂ : FinSet ℓ) ->
                  cardinality (FinSet-× S₁ S₂) == cardinality S₁ *' cardinality S₂
  cardinality-× S₁ S₂ =
    cardinality-Σ S₁ (\_ -> S₂) >=>
    cong (\x -> (finiteSumᵉ S₁ (\s -> x))) (sym *-right-one) >=>
    finiteSum-* {k = cardinality S₂} >=>
    cong (cardinality S₂ *_) (finiteSumᵉ-one S₁ >=> ℕ->Semiring-ℕ-path _) >=>
    *-commuteᵉ (cardinality S₂) (cardinality S₁)
    where
    instance
      FinSetStr-S₁ : FinSetStr (fst S₁)
      FinSetStr-S₁ = record {isFin = snd S₁}
