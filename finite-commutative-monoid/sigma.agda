{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.sigma where

open import base
open import commutative-monoid
open import cubical
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.instances
open import finsum
open import functions
open import hlevel
open import isomorphism
open import maybe
open import semiring
open import sigma
open import truncation
open import type-algebra

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  private
    finiteMerge' = finiteMerge CM
    finiteMergeᵉ' = finiteMergeᵉ CM
    finiteMerge'-convert = finiteMergeᵉ-convert CM
    finiteMerge'-⊎ = finiteMerge-⊎ CM
    finiteMerge'-Maybe = finiteMerge-Maybe CM

  module _ {ℓB : Level} {FB : Fin 0 -> FinSet ℓB}  where
    private
      B : Fin 0 -> Type ℓB
      B = fst ∘ FB

      instance
        FinSetStr-B : {z : Fin 0} -> FinSetStr (B z)
        FinSetStr-B {z} = record {isFin = snd (FB z)}

    abstract

      finiteMerge-Σ'-zero :
        (f : (Σ (Fin 0) B) -> D) ->
        finiteMergeᵉ' (FinSet-Σ (FinSet-Fin 0) FB) f ==
        finiteMergeᵉ' (FinSet-Fin 0) (\i -> finiteMergeᵉ' (FB i) (\b -> f (i , b)))
      finiteMerge-Σ'-zero f =
        finiteMerge-Uninhabited CM (¬fin-zero ∘ fst) _ >=>
        sym (finiteMerge-Uninhabited CM ¬fin-zero _)

  private
    finiteMerge-Σ' : {ℓB : Level} {n : Nat} {FB : Fin n -> FinSet ℓB}
      (f : (Σ (Fin n) (fst ∘ FB)) -> D) ->
      finiteMergeᵉ' (FinSet-Σ (FinSet-Fin n) FB) f ==
      finiteMergeᵉ' (FinSet-Fin n) (\i -> finiteMergeᵉ' (FB i) (\b -> f (i , b)))
    finiteMerge-Σ' {n = zero} {FB} f = finiteMerge-Σ'-zero f
    finiteMerge-Σ' {ℓB} {suc n} {FB} f =
      begin
        finiteMergeᵉ' (FinSet-Σ (FinSet-Fin (suc n)) FB) f
      ==< finiteMerge'-convert
            (FinSet-Σ (FinSet-Fin (suc n)) FB)
            (FinSet-⊎ (FB zero-fin)
                      (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)))
            (equiv⁻¹ (reindexΣ (equiv⁻¹ (Fin-Maybe-eq n)) B >eq> Σ-Maybe-eq)) _ >
        finiteMergeᵉ' (FinSet-⊎ (FB zero-fin)
                                (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin))) _
      ==< finiteMerge'-⊎ _ >
        finiteMergeᵉ' (FB zero-fin) g ∙
        finiteMergeᵉ' (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)) _
      ==< cong (finiteMergeᵉ' (FB zero-fin) _ ∙_) (finiteMerge-Σ' _) >
        finiteMergeᵉ' (FB zero-fin) g ∙
        finiteMergeᵉ' (FinSet-Fin n) (f' ∘ suc-fin)
      ==<>
        f' zero-fin ∙
        finiteMergeᵉ' (FinSet-Fin n) (f' ∘ suc-fin)
      ==< sym path2 >
        finiteMergeᵉ' (FinSet-Fin (suc n)) f'
      end
      where

      B : Fin (suc n) -> Type ℓB
      B i = fst (FB i)

      instance
        FinSetStr-B : {i : Fin (suc n)} -> FinSetStr (B i)
        FinSetStr-B {i} = record {isFin = snd (FB i)}

      g : {i : Fin (suc n)} -> B i -> D
      g {i} b = f (i , b)

      f' : Fin (suc n) -> D
      f' i = finiteMergeᵉ' (FB i) g

      path2 : finiteMergeᵉ' (FinSet-Fin (suc n)) f' ==
              ((f' zero-fin) ∙ finiteMergeᵉ' (FinSet-Fin n) (f' ∘ suc-fin))
      path2 =
        finiteMerge'-convert (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                             (equiv⁻¹ (Fin-Maybe-eq n)) f'
        >=> finiteMerge'-Maybe _

  module _ {ℓA ℓB : Level} (FA : FinSet ℓA) (FB : ⟨ FA ⟩ -> FinSet ℓB) where
    private
      A = fst FA
      finA = snd FA
      B : A -> Type ℓB
      B = fst ∘ FB

      instance
        FinSetStr-A : FinSetStr A
        FinSetStr-A = record {isFin = finA}
        FinSetStr-B : {a : A} -> FinSetStr (B a)
        FinSetStr-B {a} = record {isFin = snd (FB a)}

    abstract
      finiteMerge-Σ : (f : (Σ ⟨ FA ⟩ (fst ∘ FB)) -> D) ->
                      finiteMerge' f ==
                      finiteMerge' (\a -> finiteMerge' (f ∘ (a ,_)))
      finiteMerge-Σ f = unsquash (CommMonoid.isSet-Domain CM _ _) (∥-map handle finA)
        where
        handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
                 finiteMergeᵉ' (FinSet-Σ FA FB) f ==
                 finiteMergeᵉ' FA (\a -> finiteMergeᵉ' (FB a) (f ∘ (a ,_)))
        handle (n , eq) =
          finiteMerge'-convert _ _ (equiv⁻¹ (reindexΣ (equiv⁻¹ eq) B)) f
          >=> finiteMerge-Σ' _
          >=> sym (finiteMerge'-convert _ _ (equiv⁻¹ eq) _)
