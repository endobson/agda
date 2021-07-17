{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.sigma where

open import base
open import finset
open import functions
open import equivalence
open import cubical
open import sigma
open import isomorphism
open import maybe
open import type-algebra
open import fin-algebra
open import equality
open import finsum
open import finset.instances
open import fin
open import semiring
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{S : Semiring D}} where
  private
    module S = Semiring S

  module _ {ℓB : Level} {FB : Fin 0 -> FinSet ℓB}  where
    private
      B : Fin 0 -> Type ℓB
      B i = fst (FB i)
    abstract

      finiteSum-Σ'-zero :
        (f : (Σ (Fin 0) (fst ∘ FB)) -> D) ->
        finiteSum (FinSet-Σ (FinSet-Fin 0) FB) f ==
        finiteSum (FinSet-Fin 0) (\i -> finiteSum (FB i) (\b -> f (i , b)))
      finiteSum-Σ'-zero f =
        path1 >=> path2 >=> path3 >=> path4
        where
        f' : (i : Fin 0) -> B i -> D
        f' i b = f (i , b)

        g : (Fin 0) -> D
        g i = finiteSum (FB i) (f' i)

        iso1 : Iso (Σ (Fin 0) (fst ∘ FB)) Bot
        iso1 = reindexΣ-iso (equiv⁻¹ Fin-Bot-eq) B >iso> (equivToIso Σ-Bot-eq)
        iso2 : Iso (Fin 0) Bot
        iso2 = Fin-Bot-iso

        module iso1 = Iso iso1
        module iso2 = Iso iso2

        path1 :
          finiteSum (FinSet-Σ (FinSet-Fin 0) FB) f ==
          finiteSum FinSet-Bot (\x -> f (iso1.inv x))
        path1 = finiteSum-convert-iso (FinSet-Σ (FinSet-Fin 0) FB) FinSet-Bot (iso⁻¹ iso1) f

        path2 : finiteSum FinSet-Bot (f ∘ iso1.inv) == S.0#
        path2 = finiteSum-Bot (f ∘ iso1.inv)

        path3 : S.0# == finiteSum FinSet-Bot (g ∘ iso2.inv)
        path3 = sym (finiteSum-Bot _)

        path4 : finiteSum FinSet-Bot (g ∘ iso2.inv)
                == finiteSum (FinSet-Fin 0) g
        path4 = sym (finiteSum-convert-iso (FinSet-Fin 0) FinSet-Bot (iso⁻¹ iso2) g)


  --module _ {ℓB : Level} {FB : {n : Nat} -> Fin n -> FinSet ℓB}  where
  --  private
  --    B : {n : Nat} -> Fin n -> Type ℓB
  --    B = fst ∘ FB

  module _ {ℓB : Level}   where
    finiteSum-Σ' : {n : Nat}
      {FB : Fin n -> FinSet ℓB}
      (f : (Σ (Fin n) (fst ∘ FB)) -> D) ->
      finiteSum (FinSet-Σ (FinSet-Fin n) FB) f ==
      finiteSum (FinSet-Fin n) (\i -> finiteSum (FB i) (\b -> f (i , b)))
    finiteSum-Σ' {n = zero} {FB} f = finiteSum-Σ'-zero f
    finiteSum-Σ' {n = suc n} {FB} f =
      begin
        finiteSum (FinSet-Σ (FinSet-Fin (suc n)) FB) f
      ==< finiteSum-convert
            (FinSet-Σ (FinSet-Fin (suc n)) FB)
            (FinSet-⊎ (FB zero-fin)
                      (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)))
            (equiv⁻¹ (reindexΣ (equiv⁻¹ (Fin-Maybe-eq n)) B >eq> Σ-Maybe-eq)) _ >
        finiteSum (FinSet-⊎ (FB zero-fin)
                            (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin))) _
      ==< finiteSum-⊎ _ _ _ >
        finiteSum (FB zero-fin) _ S.+
        finiteSum (FinSet-Σ (FinSet-Fin n) (FB ∘ suc-fin)) _
      ==< cong (finiteSum (FB zero-fin) _ S.+_) (finiteSum-Σ' _) >
        finiteSum (FB zero-fin) g S.+
        finiteSum (FinSet-Fin n) (f' ∘ suc-fin)
      ==<>
        f' zero-fin S.+
        finiteSum (FinSet-Fin n) (f' ∘ suc-fin)
      ==< sym path2 >
        finiteSum (FinSet-Fin (suc n)) f'
      end

      where
      B : Fin (suc n) -> Type ℓB
      B i = fst (FB i)

      g : {i : Fin (suc n)} -> B i -> D
      g {i} b = f (i , b)

      f' : Fin (suc n) -> D
      f' i = finiteSum (FB i) g

      FB' : Maybe (Fin n) -> FinSet ℓB
      FB' i = FB (eqInv (Fin-Maybe-eq n) i)


      path2 : finiteSum (FinSet-Fin (suc n)) f' ==
              ((f' zero-fin) S.+
               finiteSum (FinSet-Fin n) (f' ∘ suc-fin))
      path2 =
        finiteSum-convert (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                          (equiv⁻¹ (Fin-Maybe-eq n)) f'
        >=> finiteSum-Maybe _ _

  finiteSum-Σ : {ℓA ℓB : Level} -> (FA : FinSet ℓA) -> (FB : ⟨ FA ⟩ -> FinSet ℓB)
                (f : (Σ ⟨ FA ⟩ (fst ∘ FB)) -> D) ->
                finiteSum (FinSet-Σ FA FB) f ==
                finiteSum FA (\a -> finiteSum (FB a) (f ∘ (a ,_)))
  finiteSum-Σ {ℓA} {ℓB} FA@(A , finA) FB f = unsquash (S.isSet-Domain _ _) (∥-map handle finA)
    where
    B : A -> Type ℓB
    B = fst ∘ FB

    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSum (FinSet-Σ FA FB) f ==
             finiteSum FA (\a -> finiteSum (FB a) (f ∘ (a ,_)))
    handle (n , eq) =
      finiteSum-convert _ _ (equiv⁻¹ (reindexΣ (equiv⁻¹ eq) B)) f
      >=> finiteSum-Σ' _
      >=> sym (finiteSum-convert _ _ (equiv⁻¹ eq) _)
