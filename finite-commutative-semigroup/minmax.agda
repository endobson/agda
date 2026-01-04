{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.minmax where

open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-semigroup
open import finite-commutative-semigroup.fin
open import finset.inhabited
open import finset.instances
open import functions
open import hlevel.base
open import order
open import order.minmax
open import relation
open import semigroup
open import semigroup.minmax
open import truncation

module _
  {ℓD ℓ< : Level} {D : Type ℓD} {_<_ : Rel D ℓ<} {{LO : isLinearOrder _<_}}
  {{MS : MinOperationStr LO}} where

  private
    CS : CommutativeSemigroupStr D
    CS = (CommutativeSemigroupStr-Min D)


  finite⁺Min : {ℓI : Level} {I : Type ℓI} {{FI : Fin⁺SetStr I}} ->
               (I -> D) -> D
  finite⁺Min = finite⁺Merge CS

  module _ {ℓI : Level} {I : Type ℓI} {{FI : Fin⁺SetStr I}} where

    module _ {ℓ≤ : Level} {_≤_ : Rel D ℓ≤} {{PO : isPartialOrder _≤_}}
             {{CO : CompatibleOrderStr LO PO}} where
      private
        finite⁺Min'-≤ : (n : Nat) (f : (Fin (suc n)) -> D) -> (i : Fin (suc n)) -> finite⁺Min f ≤ f i
        finite⁺Min'-≤ zero f i =
          path-≤ (finite⁺Merge-Fin1 CS f >=> cong f (snd isContrFin1 i))
        finite⁺Min'-≤ (suc n) f = fin-elim z-case s-case
          where
          split-path : finite⁺Min f == min (f zero-fin) (finite⁺Min (f ∘ suc-fin))
          split-path = finite⁺Merge-Fin CS f

          z-case : finite⁺Min f ≤ f zero-fin
          z-case = trans-=-≤ split-path min-≤-left
          s-case : (i : Fin (suc n)) -> finite⁺Min f ≤ f (suc-fin i)
          s-case i = trans-=-≤ split-path (trans-≤ min-≤-right rec)
            where
            rec : finite⁺Min (f ∘ suc-fin) ≤ f (suc-fin i)
            rec = finite⁺Min'-≤ n (f ∘ suc-fin) i


      opaque
        finite⁺Min-≤ : {f : I -> D} -> (i : I) -> finite⁺Min f ≤ f i
        finite⁺Min-≤ {f} =
          unsquash (isPropΠ (\i -> isProp-≤)) (∥-map handle (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ I))))
          where
          handle : {n : Nat} (eq : I ≃ Fin (suc n)) (i : I) -> finite⁺Min f ≤ f i
          handle {n} eq i =
            trans-=-≤ (finite⁺Merge-convert CS (equiv⁻¹ eq) f)
              (trans-≤-= (finite⁺Min'-≤ n (f ∘ eqInv eq) (eqFun eq i))
                (cong f (eqRet eq i)))

    module _ where
      private
        instance
          IPO = isLinearOrder->isPartialOrder-≯ LO
          CPO = CompatibleNegatedLinearOrder LO
      opaque
        finite⁺Min-≮ : {f : I -> D} -> (i : I) -> f i ≮ finite⁺Min f
        finite⁺Min-≮ = finite⁺Min-≤

    private
      finite⁺Min'-< : {x : D} (n : Nat) (f : (Fin (suc n)) -> D) ->
                      ((i : (Fin (suc n))) -> x < f i) -> x < finite⁺Min f
      finite⁺Min'-< zero f lt∀ =
        trans-<-= (lt∀ zero-fin) (sym (finite⁺Merge-Fin1 CS f))
      finite⁺Min'-< {x} (suc n) f lt∀ =
        trans-<-= (min-greatest-< (lt∀ zero-fin) rec)
                  (sym (finite⁺Merge-Fin CS f))
        where
        rec : x < finite⁺Min (f ∘ suc-fin)
        rec = finite⁺Min'-< n (f ∘ suc-fin) (lt∀ ∘ suc-fin)

    opaque
      finite⁺Min-< : {f : I -> D} {x : D} -> ((i : I) -> x < f i) -> x < finite⁺Min f
      finite⁺Min-< {f} {x} =
        unsquash (isPropΠ (\lt∀ -> isProp-<)) (∥-map handle (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ I))))
        where
        handle : {n : Nat} (eq : I ≃ Fin (suc n)) -> ((i : I) -> x < f i) -> x < finite⁺Min f
        handle {n} eq lt∀ =
          trans-<-= (finite⁺Min'-< n (f ∘ eqInv eq) (lt∀ ∘ eqInv eq))
                    (sym (finite⁺Merge-convert CS (equiv⁻¹ eq) f))


module _
  {ℓD ℓ< : Level} {D : Type ℓD} {_<_ : Rel D ℓ<} {{LO : isLinearOrder _<_}}
  {{MS : MaxOperationStr LO}} where

  private
    CS : CommutativeSemigroupStr D
    CS = (CommutativeSemigroupStr-Max D)

  finite⁺Max : {ℓI : Level} {I : Type ℓI} {{FI : Fin⁺SetStr I}} ->
               (I -> D) -> D
  finite⁺Max = finite⁺Merge CS

  module _ {ℓI : Level} {I : Type ℓI} {{FI : Fin⁺SetStr I}} where

    module _ {ℓ≤ : Level} {_≤_ : Rel D ℓ≤} {{PO : isPartialOrder _≤_}}
             {{CO : CompatibleOrderStr LO PO}} where
      private
        finite⁺Max'-≤ : (n : Nat) (f : (Fin (suc n)) -> D) -> (i : Fin (suc n)) -> f i ≤ finite⁺Max f
        finite⁺Max'-≤ zero f i =
          path-≤ (sym (cong f (snd isContrFin1 i)) >=>
                  sym (finite⁺Merge-Fin1 CS f))
        finite⁺Max'-≤ (suc n) f = fin-elim z-case s-case
          where
          split-path : finite⁺Max f == max (f zero-fin) (finite⁺Max (f ∘ suc-fin))
          split-path = finite⁺Merge-Fin CS f

          z-case : f zero-fin ≤ finite⁺Max f
          z-case = trans-≤-= max-≤-left (sym split-path)
          s-case : (i : Fin (suc n)) -> f (suc-fin i) ≤ finite⁺Max f
          s-case i = trans-≤-= (trans-≤ rec max-≤-right) (sym split-path)
            where
            rec : f (suc-fin i) ≤ finite⁺Max (f ∘ suc-fin)
            rec = finite⁺Max'-≤ n (f ∘ suc-fin) i

      opaque
        finite⁺Max-≤ : {f : I -> D} -> (i : I) -> f i ≤ finite⁺Max f
        finite⁺Max-≤ {f} =
          unsquash (isPropΠ (\i -> isProp-≤)) (∥-map handle (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ I))))
          where
          handle : {n : Nat} (eq : I ≃ Fin (suc n)) (i : I) -> f i ≤ finite⁺Max f
          handle {n} eq i =
            trans-=-≤ (sym (cong f (eqRet eq i)))
              (trans-≤-= (finite⁺Max'-≤ n (f ∘ eqInv eq) (eqFun eq i))
                (sym (finite⁺Merge-convert CS (equiv⁻¹ eq) f)))

    module _ where
      private
        instance
          IPO = isLinearOrder->isPartialOrder-≯ LO
          CPO = CompatibleNegatedLinearOrder LO
      opaque
        finite⁺Max-≮ : {f : I -> D} -> (i : I) -> finite⁺Max f ≮ f i
        finite⁺Max-≮ = finite⁺Max-≤

    private
      finite⁺Max'-< : {x : D} (n : Nat) (f : (Fin (suc n)) -> D) ->
                      ((i : (Fin (suc n))) -> f i < x) -> finite⁺Max f < x
      finite⁺Max'-< zero f lt∀ =
        trans-=-< (finite⁺Merge-Fin1 CS f) (lt∀ zero-fin)
      finite⁺Max'-< {x} (suc n) f lt∀ =
        trans-=-< (finite⁺Merge-Fin CS f)
                  (max-least-< (lt∀ zero-fin) rec)
        where
        rec : finite⁺Max (f ∘ suc-fin) < x
        rec = finite⁺Max'-< n (f ∘ suc-fin) (lt∀ ∘ suc-fin)

    opaque
      finite⁺Max-< : {f : I -> D} {x : D} -> ((i : I) -> f i < x) -> finite⁺Max f < x
      finite⁺Max-< {f} {x} =
        unsquash (isPropΠ (\lt∀ -> isProp-<)) (∥-map handle (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ I))))
        where
        handle : {n : Nat} (eq : I ≃ Fin (suc n)) -> ((i : I) -> f i < x) -> finite⁺Max f < x
        handle {n} eq lt∀ =
          trans-=-< (finite⁺Merge-convert CS (equiv⁻¹ eq) f)
                    (finite⁺Max'-< n (f ∘ eqInv eq) (lt∀ ∘ eqInv eq))
