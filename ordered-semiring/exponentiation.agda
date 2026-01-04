{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.exponentiation where

open import additive-group
open import base
open import equality
open import equivalence
open import nat
open import nat.even-odd
open import order
open import ordered-semiring
open import ordered-semiring.negated
open import ordered-semiring.squares
open import relation
open import semiring
open import semiring.exponentiation
open import sum
open import truncation


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}} {{PO : isPartialOrder D≤}}
         {{COS : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}} where

  opaque
    ^ℕ-preserves-0≤ : {x : D} -> 0# ≤ x -> (n : Nat) -> 0# ≤ (x ^ℕ n)
    ^ℕ-preserves-0≤ 0≤x zero = 0≤1
    ^ℕ-preserves-0≤ 0≤x (suc n) = *-preserves-0≤ 0≤x (^ℕ-preserves-0≤ 0≤x n)

    ^ℕ-0≤-preserves-≤ : {x y : D} -> 0# ≤ x -> (n : Nat) -> x ≤ y -> (x ^ℕ n) ≤ (y ^ℕ n)
    ^ℕ-0≤-preserves-≤ 0≤x zero x≤y = refl-≤
    ^ℕ-0≤-preserves-≤ 0≤x (suc n) x≤y =
      trans-≤ (*₁-preserves-≤ 0≤x (^ℕ-0≤-preserves-≤ 0≤x n x≤y))
              (*₂-preserves-≤ x≤y (^ℕ-preserves-0≤ (trans-≤ 0≤x x≤y) n))

    ^ℕ-0≤-preserves-< : {x y : D} -> 0# ≤ x -> ((n , _) : Nat⁺) ->
                        x < y -> (x ^ℕ n) < (y ^ℕ n)
    ^ℕ-0≤-preserves-< 0≤x (zero , ())
    ^ℕ-0≤-preserves-< 0≤x (suc zero , _) x<y =
      trans-=-< ^ℕ-one (trans-<-= x<y (sym ^ℕ-one))
    ^ℕ-0≤-preserves-< {x} {y} 0≤x (suc n@(suc _) , _) x<y =
      trans-≤-< (*₂-preserves-≤ (weaken-< x<y) 0≤xn) (*₁-preserves-< 0<y xn<yn)
      where
      0<y : 0# < y
      0<y = trans-≤-< 0≤x x<y
      0≤xn : 0# ≤ (x ^ℕ n)
      0≤xn = ^ℕ-preserves-0≤ 0≤x n
      xn<yn : (x ^ℕ n) < (y ^ℕ n)
      xn<yn = ^ℕ-0≤-preserves-< 0≤x (n , tt) x<y


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}} {{PO : isPartialOrder D≤}}
         {{COS : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where

  opaque
    ^ℕ-even-0≤ : (x : D) (n : Nat) -> Even n -> 0# ≤ (x ^ℕ n)
    ^ℕ-even-0≤ x zero          _ = 0≤1
    ^ℕ-even-0≤ x (suc (suc n)) e =
      trans-≤-= (*-preserves-0≤ (convert-≮ square-≮0) (^ℕ-even-0≤ x n e)) *-assoc

    ^ℕ-odd-≤0 : {x : D} -> x ≤ 0# -> (n : Nat) -> Odd n -> (x ^ℕ n) ≤ 0#
    ^ℕ-odd-≤0 {x} x≤0 (suc n) en = *₂-preserves-≤0 x≤0 (^ℕ-even-0≤ x n en)

    ^ℕ-1≤ : {x : D} -> 1# ≤ x -> (n : Nat) -> 1# ≤ (x ^ℕ n)
    ^ℕ-1≤ 1≤x n = trans-=-≤ (sym (^ℕ-preserves-1# n)) (^ℕ-0≤-preserves-≤ 0≤1 n 1≤x)

    ^ℕ-odd-1≤ : {x : D} -> 1# ≤ x -> (n : Nat) -> Odd n -> x ≤ (x ^ℕ n)
    ^ℕ-odd-1≤ {x} 1≤x (suc n) _ =
      trans-=-≤ (sym *-right-one) (*₁-preserves-≤ 0≤x (^ℕ-1≤ 1≤x n))
      where
      0≤x : 0# ≤ x
      0≤x = trans-≤ 0≤1 1≤x


module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where

  opaque
    ^ℕ-preserves-0< : {x : D} -> 0# < x -> (n : Nat) -> 0# < (x ^ℕ n)
    ^ℕ-preserves-0< 0<x zero = non-trivial-0<1 0<x
    ^ℕ-preserves-0< 0<x (suc n) = *-preserves-0< 0<x (^ℕ-preserves-0< 0<x n)

    ^ℕ-preserves-<>0 : {x : D} -> x <> 0# -> (n : Nat) -> (x ^ℕ n) <> 0#
    ^ℕ-preserves-<>0 x<>0 (suc n) =
      eqFun *-<>0-equiv (x<>0 , ^ℕ-preserves-<>0 x<>0 n)
    ^ℕ-preserves-<>0 (inj-l x<0) zero = inj-r (non-trivial-0<1 x<0)
    ^ℕ-preserves-<>0 (inj-r 0<x) zero = inj-r (non-trivial-0<1 0<x)

  module _ where
    private
      instance
        PO = isLinearOrder->isPartialOrder-≯ LO
        CPO = CompatibleNegatedLinearOrder LO
        POS = PartiallyOrderedSemiringStr-Negated S LO

    opaque
      ^ℕ-<>0-even-0< : {x : D} -> x <> 0# -> (n : Nat) -> Even n -> 0# < (x ^ℕ n)
      ^ℕ-<>0-even-0< x<>0 n en =
        proj-¬l (^ℕ-preserves-<>0 x<>0 n) (convert-≤ (^ℕ-even-0≤ _ n en))

      ^ℕ-<0-even-0< : {x : D} -> x < 0# -> (n : Nat) -> Even n -> 0# < (x ^ℕ n)
      ^ℕ-<0-even-0< x<0 = ^ℕ-<>0-even-0< (inj-l x<0)

  opaque
    ^ℕ-<0-odd-<0 : {x : D} -> x < 0# -> (n : Nat) -> Odd n -> (x ^ℕ n) < 0#
    ^ℕ-<0-odd-<0 x<0 (suc n) on = *₂-preserves-<0 x<0 (^ℕ-<0-even-0< x<0 n on)

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}} {{PO : isPartialOrder D≤}}
         {{COS : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where

  opaque
    ^ℕ-0≤-reflects-< : {x y : D} -> 0# ≤ x -> 0# ≤ y -> (n : Nat) -> (x ^ℕ n) < (y ^ℕ n) -> x < y
    ^ℕ-0≤-reflects-< {x} {y} 0≤x 0≤y zero 1<1 = bot-elim (irrefl-< 1<1)
    ^ℕ-0≤-reflects-< {x} {y} 0≤x 0≤y (suc n) x*xn<y*yn =
      unsquash isProp-< (∥-map (either case1 case2) (comparison-< _ _ _ x*xn<y*yn))
      where
      module _ (x*xn<x*yn : (x * (x ^ℕ n)) < (x * (y ^ℕ n))) where
        case1 : x < y
        case1 = ^ℕ-0≤-reflects-< 0≤x 0≤y n (*₁-reflects-< (convert-≤ 0≤x) x*xn<x*yn)

      module _ (x*yn<y*yn : (x * (y ^ℕ n)) < (y * (y ^ℕ n))) where
        case2 : x < y
        case2 = *₂-reflects-< x*yn<y*yn (convert-≤ (^ℕ-preserves-0≤ 0≤y n))

    ^ℕ-0≤-reflects-≤ : {x y : D} -> 0# ≤ x -> 0# ≤ y -> ((n , _) : Nat⁺) -> (x ^ℕ n) ≤ (y ^ℕ n) -> x ≤ y
    ^ℕ-0≤-reflects-≤ 0≤x 0≤y n x^n≤y^n =
      convert-≮ (\y<x -> convert-≤ x^n≤y^n (^ℕ-0≤-preserves-< 0≤y n y<x))
