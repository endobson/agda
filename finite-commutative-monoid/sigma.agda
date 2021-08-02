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

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) (isSet-D : isSet D) where
  open CommMonoid CM

  private
    finiteMerge' = finiteMerge CM isSet-D
    finiteMerge'-convert = finiteMerge-convert CM isSet-D
    finiteMerge'-⊎ = finiteMerge-⊎ CM isSet-D
    finiteMerge'-Maybe = finiteMerge-Maybe CM isSet-D

  module _ {ℓB : Level} {FB : Fin 0 -> FinSet ℓB}  where
    private
      B : Fin 0 -> Type ℓB
      B = fst ∘ FB
    abstract

      finiteMerge-Σ'-zero :
        (f : (Σ (Fin 0) B) -> D) ->
        finiteMerge' (FinSet-Σ (FinSet-Fin 0) FB) f ==
        finiteMerge' (FinSet-Fin 0) (\i -> finiteMerge' (FB i) (\b -> f (i , b)))
      finiteMerge-Σ'-zero f =
        finiteMerge-Uninhabited CM isSet-D _ (¬fin-zero ∘ fst) _ >=>
        sym (finiteMerge-Uninhabited CM isSet-D _ ¬fin-zero _)

  private
    finiteMerge-Σ' : {ℓB : Level} {n : Nat} {FB : Fin n -> FinSet ℓB}
      (f : (Σ (Fin n) (fst ∘ FB)) -> D) ->
      finiteMerge' (FinSet-Σ (FinSet-Fin n) FB) f ==
      finiteMerge' (FinSet-Fin n) (\i -> finiteMerge' (FB i) (\b -> f (i , b)))
    finiteMerge-Σ' {n = zero} {FB} f = finiteMerge-Σ'-zero f
    finiteMerge-Σ' {ℓB} {suc n} {FB} f =
      begin
        finiteMerge' (FinSet-Σ (FinSet-Fin (suc n)) FB) f
      ==< finiteMerge'-convert
            (FinSet-Σ (FinSet-Fin (suc n)) FB)
            (FinSet-⊎ (FB zero-fin)
                      (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)))
            (equiv⁻¹ (reindexΣ (equiv⁻¹ (Fin-Maybe-eq n)) B >eq> Σ-Maybe-eq)) _ >
        finiteMerge' (FinSet-⊎ (FB zero-fin)
                            (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin))) _
      ==< finiteMerge'-⊎ _ _ _ >
        finiteMerge' (FB zero-fin) g ∙
        finiteMerge' (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)) _
      ==< cong (finiteMerge' (FB zero-fin) _ ∙_) (finiteMerge-Σ' _) >
        finiteMerge' (FB zero-fin) g ∙
        finiteMerge' (FinSet-Fin n) (f' ∘ suc-fin)
      ==<>
        f' zero-fin ∙
        finiteMerge' (FinSet-Fin n) (f' ∘ suc-fin)
      ==< sym path2 >
        finiteMerge' (FinSet-Fin (suc n)) f'
      end
      where

      B : Fin (suc n) -> Type ℓB
      B i = fst (FB i)

      g : {i : Fin (suc n)} -> B i -> D
      g {i} b = f (i , b)

      f' : Fin (suc n) -> D
      f' i = finiteMerge' (FB i) g

      path2 : finiteMerge' (FinSet-Fin (suc n)) f' ==
              ((f' zero-fin) ∙ finiteMerge' (FinSet-Fin n) (f' ∘ suc-fin))
      path2 =
        finiteMerge'-convert (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                             (equiv⁻¹ (Fin-Maybe-eq n)) f'
        >=> finiteMerge'-Maybe _ _

  abstract
    finiteMerge-Σ : {ℓA ℓB : Level} -> (FA : FinSet ℓA) -> (FB : ⟨ FA ⟩ -> FinSet ℓB)
                    (f : (Σ ⟨ FA ⟩ (fst ∘ FB)) -> D) ->
                    finiteMerge' (FinSet-Σ FA FB) f ==
                    finiteMerge' FA (\a -> finiteMerge' (FB a) (f ∘ (a ,_)))
    finiteMerge-Σ {ℓA} {ℓB} FA@(A , finA) FB f = unsquash (isSet-D _ _) (∥-map handle finA)
      where
      B : A -> Type ℓB
      B = fst ∘ FB

      handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
               finiteMerge' (FinSet-Σ FA FB) f ==
               finiteMerge' FA (\a -> finiteMerge' (FB a) (f ∘ (a ,_)))
      handle (n , eq) =
        finiteMerge'-convert _ _ (equiv⁻¹ (reindexΣ (equiv⁻¹ eq) B)) f
        >=> finiteMerge-Σ' _
        >=> sym (finiteMerge'-convert _ _ (equiv⁻¹ eq) _)
