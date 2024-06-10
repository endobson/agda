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
open import nat.half-induction
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

module _
  {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {LO : isLinearOrder D<}
  {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
  {{AG : AdditiveGroup ACM}}
  {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  {{LOS : LinearlyOrderedSemiringStr S LO}}
  {{SOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where
  private
    instance
      ILO = LO
      IACM = ACM
      IS = S
      PO = isLinearOrder->isPartialOrder-≯ LO
      CPO = CompatibleNegatedLinearOrder LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO
      POS = PartiallyOrderedSemiringStr-Negated S LO

  private
    module _ {x y : D} (x<y : x < y) where

      acc-0<diff : {n : Nat} -> (Acc _<_ n) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
      acc-0<diff {n} (acc f) = handle (half-ind-case n)
        where
        handle : (HalfIndCase n) -> 0# < ((y ^ℕ n) + ((- x) ^ℕ n))
        handle (zero-case p) =
          trans-<-=
            (+-preserves-0< (non-trivial-0<1 x<y) (non-trivial-0<1 x<y))
            (+-cong (cong (y ^ℕ_) (sym p)) (cong ((- x) ^ℕ_) (sym p)))
        handle (even-case m _ m<n n=m+m _) =
          trans-<-= (handle2 (acc-0<diff (f m m<n))) (+-cong double-path double-path)
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

          double-path : {z : D} -> (z ^ℕ m) * (z ^ℕ m) == (z ^ℕ n)
          double-path {z} = sym (^ℕ-distrib-+-left m m) >=> (cong (z ^ℕ_) (sym n=m+m))

        handle (odd-case m _ m<n n=sm+m on) =
          trans-<-= (diff-0<⁺ (Iso.fun (same-lt x y 2m em (\_ -> 0<all-ones)) x<y))
                    (+-cong
                      (cong (y ^ℕ_) (sym n=sm+m))
                      (cong (\i -> (- (x ^ℕ i))) (sym n=sm+m) >=>
                       sym (minus-^ℕ-odd x n on)))
          where
          2m = m + m
          em : Even 2m
          em = (subst Odd n=sm+m on)
          0<all-ones = all-ones-eval-0< x y 2m (acc-0<diff (f 2m (path-≤ (sym n=sm+m)))) em

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



module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {{AG : AdditiveGroup ACM}}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{COS : CompatibleOrderStr LO PO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      ILO = LO
      IPO = PO
      IACM = ACM
      IS = S

  ^ℕ-odd-≤-1 : {x : D} -> x ≤ (- 1#) -> (n : Nat) -> Odd n -> (x ^ℕ n) ≤ x
  ^ℕ-odd-≤-1 {x} x≤-1 (suc n) en =
    trans-≤-= (*₁-flips-≤ x≤0 1≤x^n) *-right-one
    where
    1≤-x : 1# ≤ (- x)
    1≤-x = trans-=-≤ (sym minus-double-inverse) (minus-flips-≤ x≤-1)
    1≤x^n : 1# ≤ (x ^ℕ n)
    1≤x^n = trans-≤-= (^ℕ-1≤ 1≤-x n) (minus-^ℕ-even x n en)
    x≤0 : x ≤ 0#
    x≤0 = trans-≤ x≤-1 (minus-flips-0≤ (convert-≮ 1≮0))
