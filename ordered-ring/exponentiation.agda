{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation where

open import additive-group
open import additive-group.instances.nat
open import base
open import div
open import equality
open import isomorphism
open import monoid
open import nat.even-odd
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-additive-group.negated
open import ordered-ring.exponentiation.all-ones
open import ordered-ring.exponentiation.isomorphism
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.negated
open import ordered-semiring.squares
open import relation
open import ring.exponentiation
open import semiring
open import semiring.exponentiation
open import semiring.instances.nat
open import truncation

private
  data Case : Nat -> Type₀ where
    zero-case : Case zero
    even-case : (m : Nat) -> (m < (m + m)) -> Case (m + m)
    odd-case : (m : Nat) -> Even m -> Case (suc m)

  make-case : (n : Nat) -> Case n
  make-case zero = zero-case
  make-case (suc n) = handle n (fst (isContr-OddEven n))
    where
    handle : (n : Nat) -> OddEven n -> Case (suc n)
    handle n (inj-r en) = odd-case n en
    handle n (inj-l on) = handle2 (Even->div' {suc n} on)
      where
      handle2 : _ -> _
      handle2 m%sn@(m , p) = subst Case (m+m=2m >=> p) (even-case m m<2m)
        where
        0<m : 0# < m
        0<m = Pos'->< (div'-pos->pos' m%sn tt)

        m+m=2m : m + m == (m * 2)
        m+m=2m = cong (m +_) (sym *-left-one) >=> *-commuteᵉ 2 m

        m<2m : m < (m + m)
        m<2m = trans-=-< (sym (+-left-zero {m = m})) (+₂-preserves-< 0<m)

module _
  {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {LO : isLinearOrder D<}
  {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
  {{AG : AdditiveGroup ACM}}
  {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  {{LOS : LinearlyOrderedSemiringStr S LO}}
  {{SOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      ILO = LO
      IAG = AG
      IACM = ACM
      IS = S
      PO = isLinearOrder->isPartialOrder-≯ LO
      CPO = CompatibleNegatedLinearOrder LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO
      POS = PartiallyOrderedSemiringStr-Negated S LO

  private
    module _ {x y : D} (x<y : x < y) where

      acc-0<diff : {n : Nat} -> (Acc _<_ n) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
      acc-0<diff {n} (acc f) = handle (make-case n)
        where
        handle : (Case n) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
        handle zero-case = +-preserves-0< (non-trivial-0<1 x<y) (non-trivial-0<1 x<y)
        handle (even-case m m<m+m) =
          trans-<-= (handle2 (acc-0<diff (f m m<m+m))) (+-cong double-path double-path)
          where
          handle2 : (0# < ((y ^ℕ m) + ((- x) ^ℕ m))) -> _
          handle2 0<y^m+-x^m = unsquash isProp-< (∥-map handle3 (+-reflects-0< 0<y^m+-x^m))
            where
            handle3 : (0# < (y ^ℕ m)) ⊎ (0# < ((- x) ^ℕ m)) ->
                     0# < ((y ^ℕ m) * (y ^ℕ m) + ((- x) ^ℕ m) * ((- x) ^ℕ m))
            handle3 (inj-l 0<y^m) =
              trans-<-≤ (trans-<-= (*-preserves-0< 0<y^m 0<y^m) (sym +-right-zero))
                        (+₁-preserves-≤ square-≮0)
            handle3 (inj-r 0<-x^m) =
              trans-<-≤ (trans-<-= (*-preserves-0< 0<-x^m 0<-x^m) (sym +-left-zero))
                        (+₂-preserves-≤ square-≮0)

          double-path : {z : D} -> (z ^ℕ m) * (z ^ℕ m) == (z ^ℕ (m + m))
          double-path {z} =
            sym (Monoidʰ.preserves-∙ (is^ℕ.+ʰ (∃!-prop ∃!^ℕ) z) m m)

        handle (odd-case m em) =
          (trans-<-= (diff-0<⁺ (Iso.fun (same-lt x y m em (\_ -> 0<all-ones)) x<y))
                     (+-right (sym (minus-^ℕ-odd x (suc m) em))))
          where
          0<all-ones = all-ones-eval-0< x y m (acc-0<diff (f m refl-≤)) em

      wf-0<diff : (n : Nat) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
      wf-0<diff n = acc-0<diff (WellFounded-Nat< n)


  x<y<->x^n<y^n : (n : Nat) -> Odd n -> (x y : D) -> Iso (x < y) ((x ^ℕ n) < (y ^ℕ n))
  x<y<->x^n<y^n (suc n) osn x y =
    same-lt x y n osn (\x<>y -> (all-ones-eval-0< x y n (transform x<>y) osn))
    where
    to-<>0 : x <> y -> ∥ (x <> 0#) ⊎ (y <> 0#) ∥
    to-<>0 (inj-l x<y) =
      ∥-map (\{ (inj-l x<0) -> (inj-l (inj-l x<0)) ; (inj-r 0<y) -> (inj-r (inj-r 0<y))})
            (comparison-< x 0# y x<y)
    to-<>0 (inj-r y<x) =
      ∥-map (\{ (inj-l y<0) -> (inj-r (inj-l y<0)) ; (inj-r 0<x) -> (inj-l (inj-r 0<x))})
            (comparison-< y 0# x y<x)

    from-<>0 : (x <> 0#) ⊎ (y <> 0#) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
    from-<>0 (inj-l x<>0) =
      trans-<-≤ (trans-<-= (^ℕ-<>0-even-0< x<>0 n osn) (sym (minus-^ℕ-even x n osn) >=> sym +-left-zero))
                (+₂-preserves-≤ (^ℕ-even-0≤ y n osn))
    from-<>0 (inj-r y<>0) =
      trans-<-≤ (trans-<-= (^ℕ-<>0-even-0< y<>0 n osn) (sym +-right-zero))
                (+₁-preserves-≤ (^ℕ-even-0≤ (- x) n osn))

    transform : x <> y -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
    transform x<>y = unsquash isProp-< (∥-map from-<>0 (to-<>0 x<>y))
