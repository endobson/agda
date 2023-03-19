{-# OPTIONS --cubical --safe --exact-split #-}

module real.infinite-sum where

open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import nat
open import real
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import relation
open import sequence
open import sequence.partial-sums
open import sequence.permutation
open import sigma.base
open import subset
open import truncation
open import univalence

import real.series.base as ℕSeries

isCountableSet' : {ℓ : Level} -> Pred (Type ℓ) ℓ
isCountableSet' T = T ≃ Nat

isCountableSet : {ℓ : Level} -> Pred (Type ℓ) ℓ
isCountableSet T = ∥ isCountableSet' T ∥

CountableSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
CountableSet ℓ = Σ (Type ℓ) isCountableSet

Series : {ℓ : Level} -> CountableSet ℓ -> Type (ℓ-max ℓ ℓ-one)
Series (C , eq) = C -> ℝ

private
  isCS'->AbsSubtype : {ℓ : Level} {T : Type ℓ} -> isCountableSet' T -> Subtype (T -> ℝ) ℓ-one
  isCS'->AbsSubtype eq f = ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq) ,
                           ℕSeries.isProp-isConvergentSeries


  isCS->AbsSubtype : {ℓ : Level} {T : Type ℓ} -> isCountableSet T -> Subtype (T -> ℝ) ℓ-one
  isCS->AbsSubtype {ℓ} {T} ∣eq∣ =
    ∥->Set isSet-Subtype isCS'->AbsSubtype const-eval ∣eq∣
    where
    const-eval : 2-Constant isCS'->AbsSubtype
    const-eval eq1 eq2 = funExt (\f -> ΣProp-path isProp-isProp (path f))
      where
      path : (f : T -> ℝ) ->
             ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq1) ==
             ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq2)
      path f = ua (isoToEquiv (isProp->iso forward backward
                                           ℕSeries.isProp-isConvergentSeries
                                           ℕSeries.isProp-isConvergentSeries))
        where
        p : Iso ℕ ℕ
        p = equivToIso (equiv⁻¹ eq2 >eq> eq1)

        f1p : permute-seq p (f ∘ eqInv eq1) == (f ∘ eqInv eq2)
        f1p = cong (f ∘_) (funExt (\i -> eqRet eq1 (eqInv eq2 i)))

        f2p : permute-seq (iso⁻¹ p) (f ∘ eqInv eq2) == (f ∘ eqInv eq1)
        f2p = cong (f ∘_) (funExt (\i -> eqRet eq2 (eqInv eq1 i)))

        forward : ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq1) ->
                  ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq2)
        forward = subst ℕSeries.isAbsConvergentSeries f1p ∘
                  permute-preserves-isAbsConvergentSeries p
        backward : ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq2) ->
                   ℕSeries.isAbsConvergentSeries (f ∘ eqInv eq1)
        backward = subst ℕSeries.isAbsConvergentSeries f2p ∘
                   permute-preserves-isAbsConvergentSeries (iso⁻¹ p)

  Subtype-AbsConvergentSeries : {ℓ : Level} -> (C : CountableSet ℓ) -> Subtype (Series C) ℓ-one
  Subtype-AbsConvergentSeries {ℓ} C@(D , ∣eq∣) = isCS->AbsSubtype ∣eq∣

AbsConvergentSeries : {ℓ : Level} -> (C : CountableSet ℓ) -> Pred (Series C) ℓ-one
AbsConvergentSeries C s = ⟨ Subtype-AbsConvergentSeries C s ⟩

isProp-AbsConvergentSeries : {ℓ : Level} -> (C : CountableSet ℓ) -> (s : Series C) ->
                             isProp (AbsConvergentSeries C s)
isProp-AbsConvergentSeries C s = snd (Subtype-AbsConvergentSeries C s)

SeriesValuation : {ℓ : Level} {T : Type ℓ} -> Pred (T -> ℝ) (ℓ-max ℓ-one ℓ)
SeriesValuation {T = T} f =
  ∃![ v ∈ ℝ ] ((eq : T ≃ Nat) -> isLimit (partial-sums (f ∘ eqInv eq)) v)

private
  isCS'->Valuation : {ℓ : Level} {T : Type ℓ} -> (cs : isCountableSet' T) ->
                     (f : T -> ℝ) ->
                     ℕSeries.isAbsConvergentSeries (f ∘ eqInv cs) ->
                     SeriesValuation f
  isCS'->Valuation {T = T} cs f absConv = valuation , is-unique _
    where
    valuation : Σ[ v ∈ ℝ ] ((eq : T ≃ Nat) -> isLimit (partial-sums (f ∘ eqInv eq)) v)
    valuation = v , g
      where
      Σlim : ℕSeries.isConvergentSeries (f ∘ eqInv cs)
      Σlim = isAbsConvergentSeries->isConvergentSeries absConv
      v : ℝ
      v = fst Σlim
      g : (eq : T ≃ Nat) -> isLimit (partial-sums (f ∘ eqInv eq)) v
      g eq = subst (\s -> isLimit (partial-sums s) v) fp
               (permute-preserves-limit-partial-sums p absConv (snd Σlim))
        where
        p : Iso ℕ ℕ
        p = equivToIso (equiv⁻¹ eq >eq> cs)

        fp : permute-seq p (f ∘ eqInv cs) == (f ∘ eqInv eq)
        fp = cong (f ∘_) (funExt (\i -> eqRet cs (eqInv eq i)))


    is-unique : (v1 v2 : Σ[ v ∈ ℝ ] ((eq : T ≃ Nat) -> isLimit (partial-sums (f ∘ eqInv eq)) v)) ->
                v1 == v2
    is-unique (v1 , f1) (v2 , f2) =
      ΣProp-path (isPropΠ (\_ -> isProp-isLimit))
                 (cong fst (ℕSeries.isProp-isConvergentSeries (v1 , (f1 cs)) (v2 , (f2 cs))))

abstract
  ∃!infiniteSum : {ℓ : Level} -> (I : CountableSet ℓ) -> (s : Series I) ->
                  AbsConvergentSeries I s -> SeriesValuation s
  ∃!infiniteSum I@(T , ∣eq∣) s =
    ∥-elim (\ ∣eq∣ -> isPropΠ (\(_ : AbsConvergentSeries (T , ∣eq∣) s) -> isProp-isContr)) f ∣eq∣
    where
    f : (cs : isCountableSet' T) -> AbsConvergentSeries (T , ∣ cs ∣) s -> SeriesValuation s
    f cs absConv = isCS'->Valuation cs s absConv

infiniteSum : {ℓ : Level} -> (I : CountableSet ℓ) -> (s : Series I) ->
              AbsConvergentSeries I s -> ℝ
infiniteSum I s absConv = ∃!-val (∃!infiniteSum I s absConv)
