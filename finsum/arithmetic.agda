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
                        finiteSum (FinSet-Fin 0) (\i -> (f i) S.+ (g i))
                        == finiteSum (FinSet-Fin 0) f S.+ finiteSum (FinSet-Fin 0) g
    finiteSum-+'-zero =
      finiteSum-convert _ _ (equiv⁻¹ Fin-Bot-eq) _
      >=> finiteSum-Bot _
      >=> (sym S.+-right-zero)
      >=> cong2 S._+_ (sym (finiteSum-Bot _)) (sym (finiteSum-Bot _))
      >=> cong2 S._+_ (sym (finiteSum-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))
                      (sym (finiteSum-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))

    finiteSum-+' : {n : Nat} {f g : Fin n -> D} ->
                   finiteSum (FinSet-Fin n) (\i -> (f i) S.+ (g i))
                   == finiteSum (FinSet-Fin n) f S.+ finiteSum (FinSet-Fin n) g
    finiteSum-+' {n = zero} = finiteSum-+'-zero
    finiteSum-+' {n = suc n} {f} {g} =
      finiteSum-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
      >=> finiteSum-Maybe _ _
      >=> cong ((f zero-fin S.+ g zero-fin) S.+_) finiteSum-+'
      -- (f + g) + (F + G)
      >=> S.+-assoc
      -- f + (g + (F + G))
      >=> cong (_ S.+_) (sym S.+-assoc)
      -- f + ((g + F) + G)
      >=> cong (((f zero-fin) S.+_) ∘ (S._+ (finiteSum (FinSet-Fin n) (g ∘ suc-fin))))
               S.+-commute
      -- f + ((F + g) + G)
      >=> cong (_ S.+_) S.+-assoc
      -- f + (F + (g + G))
      >=> sym S.+-assoc
      -- (f + F) + (g + G)
      >=> cong2 S._+_ (sym ((finiteSum-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _) >=> finiteSum-Maybe _ _))
                      (sym ((finiteSum-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _) >=> finiteSum-Maybe _ _))


  finiteSum-+ : {f g : A -> D} -> finiteSum FA (\a -> (f a) S.+ (g a)) == finiteSum FA f S.+ finiteSum FA g
  finiteSum-+ {f} {g} = unsquash (S.isSetDomain _ _) (∥-map handle (snd FA))
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSum FA (\a -> (f a) S.+ (g a)) == finiteSum FA f S.+ finiteSum FA g
    handle (n , eq) =
      finiteSum-convert _ _ (equiv⁻¹ eq) _
      >=> finiteSum-+'
      >=> cong2 S._+_
                (sym (finiteSum-convert _ _ (equiv⁻¹ eq) _))
                (sym (finiteSum-convert _ _ (equiv⁻¹ eq) _))

  private
    finiteSum-*'-zero : {k : D} {f : Fin 0 -> D} ->
                        finiteSum (FinSet-Fin 0) (\i -> k S.* (f i))
                        == k S.* finiteSum (FinSet-Fin 0) f
    finiteSum-*'-zero {k} {f} =
      finiteSum-convert _ _ (equiv⁻¹ Fin-Bot-eq) _
      >=> finiteSum-Bot _
      >=> (sym S.*-right-zero)
      >=> cong (_ S.*_) (sym (finiteSum-Bot _))
      >=> cong (_ S.*_) (sym (finiteSum-convert _ _ (equiv⁻¹ Fin-Bot-eq) _))

    finiteSum-*' : {n : Nat} {k : D} {f : Fin n -> D} ->
                   finiteSum (FinSet-Fin n) (\i -> k S.* (f i))
                   == k S.* (finiteSum (FinSet-Fin n) f)
    finiteSum-*' {n = zero} = finiteSum-*'-zero
    finiteSum-*' {n = suc n} {k} {f}  =
      finiteSum-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
      >=> finiteSum-Maybe _ _
      >=> cong (_ S.+_) finiteSum-*'
      >=> sym (S.*-distrib-+-left)
      >=> cong (_ S.*_) (sym (finiteSum-Maybe _ _))
      >=> cong (_ S.*_) (sym (finiteSum-convert _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _))

  finiteSum-* : {k : D} {f : A -> D} -> finiteSum FA (\a -> k S.* (f a)) == k S.* finiteSum FA f
  finiteSum-* {k} {f} = unsquash (S.isSetDomain _ _) (∥-map handle (snd FA))
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
             finiteSum FA (\a -> k S.* (f a)) == k S.* (finiteSum FA f)
    handle (n , eq) =
      finiteSum-convert _ _ (equiv⁻¹ eq) _
      >=> finiteSum-*'
      >=> cong (_ S.*_) (sym (finiteSum-convert _ _ (equiv⁻¹ eq) _))
