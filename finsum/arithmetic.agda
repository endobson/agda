{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.arithmetic where

open import base
open import cubical
open import equality
open import equivalence
open import isomorphism
open import fin
open import functions
open import fin-algebra
open import finset
open import finset.instances
open import finsum
open import ring
open import semiring
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{S : Semiring D}} {ℓA : Level} {FA : FinSet ℓA} where
  private
    module S = Semiring S
    A = ⟨ FA ⟩

    finiteSum-+'-zero : {f g : Fin 0 -> D} ->
                        finiteSum (\i -> (f i) S.+ (g i))
                        == finiteSum f S.+ finiteSum g
    finiteSum-+'-zero =
      finiteSumᵉ-convert _ _ (equiv⁻¹ Fin-Bot-eq) _
      >=> finiteSum-Bot _
      >=> (sym S.+-right-zero)
      >=> cong2 S._+_ (sym (finiteSum-Bot _)) (sym (finiteSum-Bot _))
      >=> cong2 S._+_ (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))
                      (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))

    finiteSum-+' : {n : Nat} {f g : Fin n -> D} ->
                   finiteSum (\i -> (f i) S.+ (g i))
                   == finiteSum f S.+ finiteSum g
    finiteSum-+' {n = zero} = finiteSum-+'-zero
    finiteSum-+' {n = suc n} {f} {g} =
      finiteSumᵉ-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
      >=> finiteSum-Maybe _ _
      >=> cong ((f zero-fin S.+ g zero-fin) S.+_) finiteSum-+'
      -- (f + g) + (F + G)
      >=> S.+-assoc
      -- f + (g + (F + G))
      >=> cong (_ S.+_) (sym S.+-assoc)
      -- f + ((g + F) + G)
      >=> cong (((f zero-fin) S.+_) ∘ (S._+ (finiteSum (g ∘ suc-fin))))
               S.+-commute
      -- f + ((F + g) + G)
      >=> cong (_ S.+_) S.+-assoc
      -- f + (F + (g + G))
      >=> sym S.+-assoc
      -- (f + F) + (g + G)
      >=> cong2 S._+_ (sym ((finiteSumᵉ-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _) >=> finiteSum-Maybe _ _))
                      (sym ((finiteSumᵉ-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _) >=> finiteSum-Maybe _ _))


  finiteSum-+ : {f g : A -> D} -> finiteSumᵉ FA (\a -> (f a) S.+ (g a)) ==
                                  finiteSumᵉ FA f S.+ finiteSumᵉ FA g
  finiteSum-+ {f} {g} = unsquash (S.isSet-Domain _ _) (∥-map handle (snd FA))
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSumᵉ FA (\a -> (f a) S.+ (g a)) == finiteSumᵉ FA f S.+ finiteSumᵉ FA g
    handle (n , eq) =
      finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _
      >=> finiteSum-+'
      >=> cong2 S._+_
                (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _))
                (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _))

  private
    finiteSum-*'-zero : {k : D} {f : Fin 0 -> D} ->
                        finiteSum (\i -> k S.* (f i))
                        == k S.* finiteSum f
    finiteSum-*'-zero {k} {f} =
      finiteSumᵉ-convert _ _ (equiv⁻¹ Fin-Bot-eq) _
      >=> finiteSum-Bot _
      >=> (sym S.*-right-zero)
      >=> cong (_ S.*_) (sym (finiteSum-Bot _))
      >=> cong (_ S.*_) (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))

    finiteSum-*' : {n : Nat} {k : D} {f : Fin n -> D} ->
                   finiteSum (\i -> k S.* (f i))
                   == k S.* (finiteSum f)
    finiteSum-*' {n = zero} = finiteSum-*'-zero
    finiteSum-*' {n = suc n} {k} {f}  =
      finiteSumᵉ-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
      >=> finiteSum-Maybe _ _
      >=> cong (_ S.+_) finiteSum-*'
      >=> sym (S.*-distrib-+-left)
      >=> cong (_ S.*_) (sym (finiteSum-Maybe _ _))
      >=> cong (_ S.*_) (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _))

  finiteSum-* : {k : D} {f : A -> D} -> finiteSumᵉ FA (\a -> k S.* (f a)) == k S.* finiteSumᵉ FA f
  finiteSum-* {k} {f} = unsquash (S.isSet-Domain _ _) (∥-map handle (snd FA))
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSumᵉ FA (\a -> k S.* (f a)) == k S.* (finiteSumᵉ FA f)
    handle (n , eq) =
      finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _
      >=> finiteSum-*'
      >=> cong (_ S.*_) (sym (finiteSumᵉ-convert _ _ (equiv⁻¹ eq) _))
