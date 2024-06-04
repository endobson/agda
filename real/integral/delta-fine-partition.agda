{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.delta-fine-partition where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.real
open import base
open import equality
open import fin
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.rational
open import real.heyting-field
open import real.integral.partition
open import real.integral.partition-index
open import real.interval
open import real.order
open import real.rational
open import ring
open import ring.implementations.real
open import semiring
open import truncation

import int

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

  module _ {a b : ℝ} (a' b' : ℚ) (aU-a' : Real.U a a') (bL-b' : Real.L b b') (a'<b' :  a' < b') where
    private
      module _ (n⁺ : Nat⁺) where
        private
          n = fst n⁺

        u : Fin (suc n) -> ℚ
        u (i , _) = (ℕ->ℚ i * 1/ℕ n⁺) * (diff a' b') + a'


        u0=a' : u zero-fin == a'
        u0=a' =
          +-left (*-left *-left-zero >=> *-left-zero) >=> +-left-zero

        un=b' : u (n , refl-≤) == b'
        un=b' =
          +-left (*-left (*-commute >=> (1/ℕ-ℕ-path n⁺)) >=>
                  *-left-one) >=>
          +-commute >=>
          diff-step

        udiff : (i : Fin n) -> diff (u (inc-fin i)) (u (suc-fin i)) == (1/ℕ n⁺) * (diff a' b')
        udiff i =
          sym +-swap-diff >=>
          +-right +-inverse >=>
          +-right-zero >=>
          sym *-distrib-diff-right >=>
          *-left (sym *-distrib-diff-right >=>
                  *-left i-path >=>
                  *-left-one)
          where
          i-path : diff (ℕ->ℚ (Fin.i (inc-fin i)))
                        (ℕ->ℚ (Fin.i (suc-fin i))) == 1#
          i-path = sym (ℤ->ℚ-preserves-diff _ _) >=>
                   cong ℤ->ℚ (int.add1-extract-left >=> cong int.add1 +-inverse)

      0<diff-a'b' : 0# < diff a' b'
      0<diff-a'b' = trans-=-< (sym +-inverse) (+₂-preserves-< a'<b')

      harmonic-partition : Nat⁺ -> Partition a b
      harmonic-partition n⁺@(n@(suc _) , _) =
        record
        { n = n
        ; u = u n⁺
        ; aU-u0 = subst (Real.U a) (sym (u0=a' n⁺)) aU-a'
        ; bL-un = subst (Real.L b) (sym (un=b' n⁺)) bL-b'
        ; u<u = u<u
        }
        where

        u<u : (i : Fin n) -> u n⁺ (inc-fin i) < u n⁺ (suc-fin i)
        u<u _ =
          +₂-preserves-< (*₂-preserves-<
            (*₂-preserves-<
              (ℕ->ℚ-preserves-< refl-≤)
              (Pos-1/ℕ n⁺))
            0<diff-a'b')

    rational-bounds->∃δFinePartition :
      (δ : ℝ⁺) -> diff a (ℚ->ℝ a') ≤ ⟨ δ ⟩ -> diff (ℚ->ℝ b') b ≤ ⟨ δ ⟩ ->
      ∃ (Partition a b) (isδFine ⟨ δ ⟩)
    rational-bounds->∃δFinePartition (δ , 0<δ) da≤δ db≤δ =
      ∥-bind handle 0<δ
      where
      handle : (0# ℝ<' δ) -> ∃ (Partition a b) (isδFine δ)
      handle (ℝ<'-cons δ' 0U-δ' δL-δ') = ∥-map handle2 (small-1/ℕ (δ2 , 0<δ2))
        where
        1/ab : ℚ
        1/ab = r1/ (diff a' b') (\p -> irrefl-path-< (sym p) 0<diff-a'b')

        δ2 = δ' * 1/ab
        0<δ2 : 0# < δ2
        0<δ2 = *-preserves-0< (U->ℚ< 0U-δ') (r1/-preserves-Pos (diff a' b') _ 0<diff-a'b')

        handle2 : Σ[ n ∈ Nat⁺ ] (1/ℕ n < δ2) -> Σ (Partition a b) (isδFine δ)
        handle2 (n@(suc _ , _) , 1/n<δ2) = p , fine
          where
          p = (harmonic-partition n)
          fine : isδFine δ _
          fine pi-low = trans-=-≤ (+-left (cong ℚ->ℝ (u0=a' n))) da≤δ
          fine pi-high = trans-=-≤ (cong (\x -> diff x b) (cong ℚ->ℝ (un=b' n))) db≤δ
          fine (pi-mid i) =
            weaken-<
              (trans-<
                (trans-=-<
                   (sym ℚ->ℝ-preserves-diff >=> cong ℚ->ℝ (udiff n i))
                   (ℚ->ℝ-preserves-< (trans-<-= (*₂-preserves-< 1/n<δ2 0<diff-a'b')
                                                (*-assoc >=>
                                                 *-right (r1/-inverse _ _) >=>
                                                 *-right-one))))
                (L->ℝ< δL-δ'))

  ∃δFinePartition' : {a b : ℝ} -> a < b -> (δ : ℝ⁺) -> ∃ (Partition a b) (isδFine ⟨ δ ⟩)
  ∃δFinePartition' {a} {b} a<b (δ , 0<δ) = ∥-bind handle 0<δ2
    where
    ab/2 = (diff a b) * 1/2ℝ

    0<ab : 0# < diff a b
    0<ab = trans-=-< (sym +-inverse) (+₂-preserves-< a<b)

    δ2 = min ab/2 δ
    0<δ2 : 0# < δ2
    0<δ2 = min-greatest-< (*-preserves-0< 0<ab 0<1/2ℝ) 0<δ

    handle : (0# ℝ<' δ2) -> ∃ (Partition a b) (isδFine δ)
    handle (ℝ<'-cons δ2' 0U-δ2' δ2L-δ2') =
      ∥-bind2 handle2 (find-small-ℝ∈Iℚ a (δ2' , U->ℚ< 0U-δ2'))
                      (find-small-ℝ∈Iℚ b (δ2' , U->ℚ< 0U-δ2'))
      where
      handle2 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ a qi × i-width qi ≤ δ2') ->
                Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ b qi × i-width qi ≤ δ2') ->
                ∃ (Partition a b) (isδFine δ)
      handle2 (ai@(Iℚ-cons al au al<au) , (aL-al , aU-au) , w-ai≤δ2')
              (bi@(Iℚ-cons bl bu bl<bu) , (bL-bl , bU-bu) , w-bi≤δ2') =
        rational-bounds->∃δFinePartition au bl aU-au bL-bl au<bl (δ , 0<δ) diff-aau≤δ diff-blb≤δ
          where
          diff-aal<0 : diff a (ℚ->ℝ al) < 0#
          diff-aal<0 = trans-<-= (+₂-preserves-< (L->ℝ< aL-al)) +-inverse

          diff-bub<0 : diff (ℚ->ℝ bu) b < 0#
          diff-bub<0 = trans-<-= (+₂-preserves-< (U->ℝ< bU-bu)) +-inverse

          diff-aau≤δ : diff a (ℚ->ℝ au) ≤ δ
          diff-aau≤δ =
            trans-=-≤ (sym diff-trans)
              (trans-≤-= (+-preserves-≤ (weaken-< diff-aal<0)
                                        (trans-=-≤ (sym ℚ->ℝ-preserves-diff)
                                                   (trans-≤ (ℚ->ℝ-preserves-≤ w-ai≤δ2')
                                                            (trans-≤ (weaken-< (L->ℝ< δ2L-δ2'))
                                                                     min-≤-right))))
                         +-left-zero)

          diff-blb≤δ : diff (ℚ->ℝ bl) b ≤ δ
          diff-blb≤δ =
            trans-=-≤ (sym diff-trans)
              (trans-≤-= (+-preserves-≤ (trans-=-≤ (sym ℚ->ℝ-preserves-diff)
                                                   (trans-≤ (ℚ->ℝ-preserves-≤ w-bi≤δ2')
                                                            (trans-≤ (weaken-< (L->ℝ< δ2L-δ2'))
                                                                     min-≤-right)))
                                        (weaken-< diff-bub<0))
                         +-right-zero)


          au<bl : au < bl
          au<bl = handle3 (split-< au bl)
            where
            handle3 : (au < bl) ⊎ (bl ≤ au) -> au < bl
            handle3 (inj-l au<bl) = au<bl
            handle3 (inj-r bl≤au) =
              bot-elim (albu≤diff-ab diff-ab<albu)
              where
              diff-path : diff al bu == diff al au + (diff au bl + diff bl bu)
              diff-path = sym diff-trans >=> +-right (sym diff-trans)

              albu≤ : diff al bu ≤ (δ2' + δ2')
              albu≤ =
                trans-=-≤ diff-path
                  (+-preserves-≤ w-ai≤δ2'
                    (trans-≤-= (+-preserves-≤ (trans-≤-= (+₂-preserves-≤ bl≤au) +-inverse)
                                              w-bi≤δ2')
                               +-left-zero))


              δ2'<ab/2 : ℚ->ℝ δ2' ≤ ab/2
              δ2'<ab/2 = weaken-< (trans-<-≤ (L->ℝ< δ2L-δ2') min-≤-left)

              albu≤diff-ab : ℚ->ℝ (diff al bu) ≤ diff a b
              albu≤diff-ab =
                trans-≤ (ℚ->ℝ-preserves-≤ albu≤)
                  (trans-=-≤ ℚ->ℝ-preserves-+ (trans-≤-= (+-preserves-≤ δ2'<ab/2 δ2'<ab/2)
                                                         (sym *-distrib-+-left >=>
                                                          *-right 1/2ℝ-1-path >=> *-right-one)))

              diff-ab-path : diff a b == diff a (ℚ->ℝ al) + (ℚ->ℝ (diff al bu) + diff (ℚ->ℝ bu) b)
              diff-ab-path =
                sym diff-trans >=>
                +-right (sym diff-trans >=> +-left (sym ℚ->ℝ-preserves-diff))

              diff-ab<albu : diff a b < ℚ->ℝ (diff al bu)
              diff-ab<albu =
                trans-=-< diff-ab-path
                  (trans-<-= (+-preserves-< diff-aal<0 (+₁-preserves-< diff-bub<0))
                             (+-left-zero >=> +-right-zero))

abstract
  ∃δFinePartition : {a b : ℝ} -> a < b -> (δ : ℝ⁺) -> ∃ (Partition a b) (isδFine ⟨ δ ⟩)
  ∃δFinePartition = ∃δFinePartition'
