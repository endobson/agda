{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.open-interval where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import functions
open import funext
open import nat
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import rational
open import rational.open-interval
open import real
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.order
open import real.rational
open import real.sequence.cauchy
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import sequence

module _ (s : Sequence Iℚ)
         (step-⊆ : ∀ n -> s (suc n) i⊆ s n)
         (lim-width : isLimit (ℚ->ℝ ∘ i-width ∘ s) 0#) where
  private
    s⊆ : ∀ {n1 n2} -> n1 ≤ n2 -> s n2 i⊆ s n1
    s⊆ {n1} {n2} (i , path) = handle i n1 path
      where
      handle : (i n1 : ℕ) -> i + n1 == n2 -> s n2 i⊆ s n1
      handle zero _ path =
        i⊆-cons (path-≤ (\i -> Iℚ.l (s (path i))))
                (path-≤ (\i -> Iℚ.u (s (path (~ i)))))
      handle (suc i) n1 path =
        trans-i⊆ (handle i (suc n1) (+'-right-suc >=> path))
                 (step-⊆ n1)

    ls : Sequence ℝ
    ls = ℚ->ℝ ∘ Iℚ.l ∘ s
    us : Sequence ℝ
    us = ℚ->ℝ ∘ Iℚ.u ∘ s

    isCauchy'-ls : isCauchy' ls
    isCauchy'-ls (ε , 0<ε) =
      ∀Largeℕ-map handle (isLimit.upper lim-width ε (ℚ<->U 0<ε))
      where
      -ε<0 = minus-flips-0< 0<ε
      width : ℕ -> ℝ
      width i = (ℚ->ℝ (i-width (s i)))
      handle : {n : Nat} -> (Real.U (width n) ε) ->
               (m : Nat) -> n ≤ m -> εBounded ε (diff (ls n) (ls m))
      handle {n} widthU m n≤m =
        (ℝ<->L -ε<dls) , trans-ℝ≤-U dls≤width widthU
        where
        dls = diff (ls n) (ls m)
        dus = diff (us n) (us m)
        lsn≤lsm : ls n ≤ ls m
        lsn≤lsm = ℚ->ℝ-preserves-≤ (_i⊆_.l (s⊆ n≤m))
        0≤dls : 0# ≤ dls
        0≤dls = diff-0≤⁺ lsn≤lsm
        -ε<dls : ℚ->ℝ (- ε) < dls
        -ε<dls = trans-<-≤ (ℚ->ℝ-preserves-< -ε<0) 0≤dls

        diff-path' : diff (ls n) (ls m) ==
                    diff (ls n) (us n) + diff (us n) (ls m)
        diff-path' = sym diff-trans

        d2≤0 : diff (us n) (ls m) ≤ 0#
        d2≤0 = diff-≤0⁺ usn≤lsm
          where
          usm≤usn : us m ≤ us n
          usm≤usn = ℚ->ℝ-preserves-≤ (_i⊆_.u (s⊆ n≤m))
          usn≤lsm : ls m ≤ us n
          usn≤lsm = weaken-< (trans-<-≤ (ℚ->ℝ-preserves-< (Iℚ.l<u (s m))) usm≤usn)

        dn=width-n : diff (ls n) (us n) == ℚ->ℝ (i-width (s n))
        dn=width-n = sym ℚ->ℝ-preserves-diff
        dls≤width : dls ≤ width n
        dls≤width =
          trans-=-≤ diff-path'
            (trans-≤-= (+-preserves-≤ (path-≤ dn=width-n) d2≤0) +-right-zero)

    isCauchy-ls : isCauchy ls
    isCauchy-ls = isCauchy'->isCauchy isCauchy'-ls

  opaque
    Iℚs->ℝ : ℝ
    Iℚs->ℝ = fst (isCauchy->isConvergentSequence isCauchy-ls)

    Iℚs->ℝ-lower-limit : isLimit (\i -> ℚ->ℝ (Iℚ.l (s i))) Iℚs->ℝ
    Iℚs->ℝ-lower-limit = snd (isCauchy->isConvergentSequence isCauchy-ls)

    Iℚs->ℝ-upper-limit : isLimit (\i -> ℚ->ℝ (Iℚ.u (s i))) Iℚs->ℝ
    Iℚs->ℝ-upper-limit =
      subst2 isLimit (funExt (\i -> sym ℚ->ℝ-preserves-+ >=> cong ℚ->ℝ diff-step)) +-right-zero
        (+-preserves-limit Iℚs->ℝ-lower-limit lim-width)
