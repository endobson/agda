{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.arithmetic where

open import additive-group
open import apartness
open import base
open import commutative-monoid
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.instances
open import finsum
open import functions
open import isomorphism
open import semiring
open import sigma
open import truncation


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
  where
  private
    instance
      IACM = ACM
    module ACM = AdditiveCommMonoid ACM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    abstract
      finiteSum-- : {f : I -> D} -> finiteSum (\i -> - (f i)) == - (finiteSum f)
      finiteSum-- = finiteMerge-homo-inject -ʰ
        where
        -ʰ : CommMonoidʰᵉ ACM.comm-monoid ACM.comm-monoid -_
        -ʰ = record
          { preserves-ε = minus-zero
          ; preserves-∙ = minus-distrib-plusᵉ
          }

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
  where
  private
    module S = Semiring S
    instance
      IACM = ACM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    abstract
      finiteSum-* : {k : D} {f : I -> D} -> finiteSum (\i -> k * (f i)) == k * finiteSum f
      finiteSum-* = finiteMerge-homo-inject k*ʰ
        where
        k*ʰ : {k : D} -> CommMonoidʰᵉ S.+-CommMonoid S.+-CommMonoid (k *_)
        k*ʰ {k} = record
          { preserves-ε = *-right-zero
          ; preserves-∙ = \_ _ -> *-distrib-+-left
          }

  module _ {ℓ# : Level} {AG : AdditiveGroup ACM} {A : TightApartnessStr D ℓ#}
           {{AAG : ApartAdditiveGroup AG A}}  where
    private
      instance
        IA = A

      finiteSum'-#0 : (n : Nat) (f : Fin n -> D) -> finiteSum f # 0# -> ∃[ i ∈ Fin n ] (f i # 0#)
      finiteSum'-#0 zero f sum#0 = bot-elim (irrefl-path-# (finiteMerge-Fin0 _ f) sum#0)
      finiteSum'-#0 (suc n) f sum#0 =
        ∥-bind handle (+-reflects-#0 (subst (_# 0#) (finiteMerge-FinSuc _ f) sum#0))
        where
        handle : (f zero-fin # 0#) ⊎ (finiteSum (f ∘ suc-fin) # 0#) -> ∃[ i ∈ Fin (suc n) ] (f i # 0#)
        handle (inj-l f0#0) = ∣ zero-fin , f0#0 ∣
        handle (inj-r sum#0) = ∥-map (\ { (i , fsi#0 ) -> suc-fin i , fsi#0 })
                                     (finiteSum'-#0 n (f ∘ suc-fin) sum#0)

    module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
      finiteSum-#0 : {f : I -> D} -> finiteSum f # 0# -> ∃[ i ∈ I ] (f i # 0#)
      finiteSum-#0 {f} sum#0 = ∥-bind handle (FinSetStr.isFin FI)
        where
        handle : Σ[ n ∈ Nat ] (I ≃ Fin n) -> ∃[ i ∈ I ] (f i # 0#)
        handle (n , eq) = ∥-map (eqInv (reindexΣ (equiv⁻¹ eq) _))
                                (finiteSum'-#0 n _ (subst (_# 0#) p sum#0))
          where
          p : finiteSum f == finiteSum (f ∘ (eqInv eq))
          p = finiteMerge-convert _ (equiv⁻¹ eq) f
