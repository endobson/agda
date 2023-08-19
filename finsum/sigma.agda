{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.sigma where

open import additive-group
open import base
open import finset
open import functions
open import sigma
open import isomorphism
open import type-algebra
open import fin-algebra
open import equality
open import equivalence
open import finsum
open import finite-commutative-monoid.instances
open import finset.instances
open import finset.instances.base
open import fin
open import semiring
open import truncation

open EqReasoning

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    module S = Semiring S
    instance
      IACM = ACM

  module _ {ℓB : Level} {FB : Fin 0 -> FinSet ℓB}  where
    private
      B : Fin 0 -> Type ℓB
      B i = fst (FB i)
    abstract

      finiteSum-Σ'-zero :
        (f : (Σ (Fin 0) (fst ∘ FB)) -> D) ->
        finiteSumᵉ (FinSet-Σ (FinSet-Fin 0) FB) f ==
        finiteSumᵉ (FinSet-Fin 0) (\i -> finiteSumᵉ (FB i) (\b -> f (i , b)))
      finiteSum-Σ'-zero f =
        path1 >=> path2 >=> path3 >=> path4
        where
        f' : (i : Fin 0) -> B i -> D
        f' i b = f (i , b)

        g : (Fin 0) -> D
        g i = finiteSumᵉ (FB i) (f' i)

        iso1 : Iso (Σ (Fin 0) (fst ∘ FB)) Bot
        iso1 = reindexΣ-iso (equiv⁻¹ Fin-Bot-eq) B >iso> (equivToIso Σ-Bot-eq)
        iso2 : Iso (Fin 0) Bot
        iso2 = Fin-Bot-iso

        module iso1 = Iso iso1
        module iso2 = Iso iso2

        path1 :
          finiteSumᵉ (FinSet-Σ (FinSet-Fin 0) FB) f ==
          finiteSumᵉ FinSet-Bot (\x -> f (iso1.inv x))
        path1 = finiteSumᵉ-convert-iso (FinSet-Σ (FinSet-Fin 0) FB) FinSet-Bot (iso⁻¹ iso1) f

        path2 : finiteSumᵉ FinSet-Bot (f ∘ iso1.inv) == 0#
        path2 = finiteSum-Bot (f ∘ iso1.inv)

        path3 : 0# == finiteSumᵉ FinSet-Bot (g ∘ iso2.inv)
        path3 = sym (finiteSum-Bot _)

        path4 : finiteSumᵉ FinSet-Bot (g ∘ iso2.inv)
                == finiteSumᵉ (FinSet-Fin 0) g
        path4 = sym (finiteSumᵉ-convert-iso (FinSet-Fin 0) FinSet-Bot (iso⁻¹ iso2) g)


  --module _ {ℓB : Level} {FB : {n : Nat} -> Fin n -> FinSet ℓB}  where
  --  private
  --    B : {n : Nat} -> Fin n -> Type ℓB
  --    B = fst ∘ FB

  module _ {ℓB : Level}   where
    finiteSum-Σ' : {n : Nat}
      {FB : Fin n -> FinSet ℓB}
      (f : (Σ (Fin n) (fst ∘ FB)) -> D) ->
      finiteSumᵉ (FinSet-Σ (FinSet-Fin n) FB) f ==
      finiteSumᵉ (FinSet-Fin n) (\i -> finiteSumᵉ (FB i) (\b -> f (i , b)))
    finiteSum-Σ' {n = zero} {FB} f = finiteSum-Σ'-zero f
    finiteSum-Σ' {n = suc n} {FB} f =
      begin
        finiteSumᵉ (FinSet-Σ (FinSet-Fin (suc n)) FB) f
      ==< finiteSumᵉ-convert
            (FinSet-Σ (FinSet-Fin (suc n)) FB)
            (FinSet-⊎ (FB zero-fin)
                      (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)))
            (equiv⁻¹ (reindexΣ (equiv⁻¹ (Fin-Maybe-eq n)) B >eq> Σ-Maybe-eq)) _ >
        finiteSumᵉ (FinSet-⊎ (FB zero-fin)
                            (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin))) _
      ==< finiteMerge-⊎ _ {{_}} {{_}} _ >
        finiteSumᵉ (FB zero-fin) _ +
        finiteSumᵉ (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)) _
      ==< cong (finiteSumᵉ (FB zero-fin) _ +_) (finiteSum-Σ' _) >
        finiteSumᵉ (FB zero-fin) g +
        finiteSumᵉ (FinSet-Fin n) (f' ∘ suc-fin)
      ==<>
        f' zero-fin +
        finiteSumᵉ (FinSet-Fin n) (f' ∘ suc-fin)
      ==< sym path2 >
        finiteSumᵉ (FinSet-Fin (suc n)) f'
      end

      where
      B : Fin (suc n) -> Type ℓB
      B i = fst (FB i)

      g : {i : Fin (suc n)} -> B i -> D
      g {i} b = f (i , b)

      f' : Fin (suc n) -> D
      f' i = finiteSumᵉ (FB i) g

      path2 : finiteSumᵉ (FinSet-Fin (suc n)) f' ==
              ((f' zero-fin) +
               finiteSumᵉ (FinSet-Fin n) (f' ∘ suc-fin))
      path2 =
        finiteSumᵉ-convert (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                          (equiv⁻¹ (Fin-Maybe-eq n)) f'
        >=> finiteMerge-Maybe _ _

  finiteSum-Σ : {ℓA ℓB : Level} -> (FA : FinSet ℓA) -> (FB : ⟨ FA ⟩ -> FinSet ℓB)
                (f : (Σ ⟨ FA ⟩ (fst ∘ FB)) -> D) ->
                finiteSumᵉ (FinSet-Σ FA FB) f ==
                finiteSumᵉ FA (\a -> finiteSumᵉ (FB a) (f ∘ (a ,_)))
  finiteSum-Σ {ℓA} {ℓB} FA@(A , finA) FB f = unsquash (S.isSet-Domain _ _) (∥-map handle finA)
    where
    B : A -> Type ℓB
    B = fst ∘ FB

    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSumᵉ (FinSet-Σ FA FB) f ==
             finiteSumᵉ FA (\a -> finiteSumᵉ (FB a) (f ∘ (a ,_)))
    handle (n , eq) =
      finiteSumᵉ-convert _ _ (equiv⁻¹ (reindexΣ (equiv⁻¹ eq) B)) f
      >=> finiteSum-Σ' _
      >=> sym (finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _)
