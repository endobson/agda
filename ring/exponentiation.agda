{-# OPTIONS --cubical --safe --exact-split #-}

module ring.exponentiation where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import group
open import group.int
open import int.add1
open import int.addition
open import int.base
open import int.elimination
open import int.order
open import int.sign
open import monoid
open import nat
open import nat.even-odd
open import order
open import order.instances.int
open import ring
open import semiring
open import semiring.exponentiation
open import semiring.unit
open import sigma.base


module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}}
  where

  minus-^ℕ-odd : (x : D) (n : Nat) -> (Odd n) -> (- x) ^ℕ n == - (x ^ℕ n)
  minus-^ℕ-odd x (suc zero) _ = *-right-one >=> cong -_ (sym *-right-one)
  minus-^ℕ-odd x (suc (suc i)) oi =
    sym *-assoc >=> *-left minus-extract-both >=>
    *-right (minus-^ℕ-odd x i oi) >=>
    minus-extract-right >=>
    cong -_ *-assoc

  minus-^ℕ-even : (x : D) (n : Nat) -> (Even n) -> (- x) ^ℕ n == x ^ℕ n
  minus-^ℕ-even x zero _ = refl
  minus-^ℕ-even x (suc (suc i)) ei =
    sym *-assoc >=> *-left minus-extract-both >=>
    *-right (minus-^ℕ-even x i ei) >=>
    *-assoc

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}}
         where
  _u^ℤ_ : Unit D -> ℤ -> Unit D
  a u^ℤ (nonneg n) = a u^ℕ n
  a u^ℤ (neg n) = u1/ (a u^ℕ (suc n))

  private
    opaque
      u^ℤ-add1 : (u : Unit D) (x : ℤ) -> u u^ℤ (add1 x) == u u* (u u^ℤ x)
      u^ℤ-add1 u (nonneg n) = refl
      u^ℤ-add1 u@(u' , (is-unit inv p))  (neg zero) = path
        where
        path : 1u == u u* (u1/ (u u^ℕ (suc zero)))
        path = unit-path (sym p) >=> (cong (\x -> (u u* (u1/ x))) (sym u^ℕ-one))
      u^ℤ-add1 u (neg (suc n)) = sym path
        where
        path : u u* (u1/ (u u* (u u^ℕ (suc n)))) == (u1/ (u u^ℕ (suc n)))
        path =
          cong (u u*_) u1/-distrib-u*
          >=> sym u*-assoc
          >=> cong (_u* (u1/ (u u^ℕ (suc n)))) u*-right-inverse
          >=> u*-left-one

  opaque
    u^ℤ-sub1 : (u : Unit D) (x : ℤ) -> u u^ℤ (sub1 x) == (u1/ u) u* (u u^ℤ x)
    u^ℤ-sub1 u (nonneg zero) = unit-path refl
    u^ℤ-sub1 u (nonneg (suc n)) =
      sym u*-left-one >=>
      cong (_u* (u u^ℤ (int n))) (sym u*-left-inverse) >=>
      u*-assoc
    u^ℤ-sub1 u (neg n) =
      cong u1/ (u^ℤ-add1 u (int (suc n))) >=> u1/-distrib-u*


  private
    opaque
      u^ℤ-preserves-inverse : {b : Unit D} {x : ℤ} -> (b u^ℤ (- x)) == u1/ (b u^ℤ x)
      u^ℤ-preserves-inverse {x = zero-int} = unit-path refl
      u^ℤ-preserves-inverse {x = pos x} = refl
      u^ℤ-preserves-inverse {x = neg x} = unit-path refl

      u^ℤ-distrib-+-NonNeg : {b : Unit D} {x y : ℤ} -> NonNeg x ->
                             b u^ℤ (x + y) == (b u^ℤ x) u* (b u^ℤ y)
      u^ℤ-distrib-+-NonNeg {b} {zero-int} _ =
        cong (b u^ℤ_) +-left-zero >=> sym u*-left-one
      u^ℤ-distrib-+-NonNeg {b} {nonneg (suc x)} {y} _ =
        cong (b u^ℤ_) add1-extract-left
        >=> u^ℤ-add1 b ((int x) + y)
        >=> cong (b u*_) (u^ℤ-distrib-+-NonNeg {b} {nonneg x} {y} 0≤nonneg)
        >=> sym u*-assoc
        >=> cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b (int x)))
      u^ℤ-distrib-+-NonNeg {b} {neg x} 0≤x = bot-elim (convert-≤ 0≤x neg<0)


      u^ℤ-distrib-+ : {b : Unit D} {x y : ℤ} -> b u^ℤ (x + y) == (b u^ℤ x) u* (b u^ℤ y)
      u^ℤ-distrib-+ {b} {x} {y} = IntElim-add1sub1-elim z add1-case sub1-case x
        where
        P : ℤ -> Type ℓD
        P x = b u^ℤ (x + y) == (b u^ℤ x) u* (b u^ℤ y)

        z : P (int 0)
        z = cong (b u^ℤ_) +-left-zero >=> sym u*-left-one
        add1-case : (x : ℤ) -> (P x) -> (P (add1 x))
        add1-case x p =
          cong (b u^ℤ_) (add1-extract-left) >=>
          u^ℤ-add1 b (x + y) >=> cong (b u*_) p >=>
          sym u*-assoc >=>
          cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b x))

        sub1-case : (x : ℤ) -> (P x) -> (P (sub1 x))
        sub1-case x p =
          cong (b u^ℤ_) sub1-extract-left >=>
          u^ℤ-sub1 b (x + y) >=> cong ((u1/ b) u*_) p >=>
          sym u*-assoc >=>
          cong (_u* (b u^ℤ y)) (sym (u^ℤ-sub1 b x))

      isGroupʰ-u^ℤ : (base : Unit D) -> isGroupʰ ℤ-Group (UnitGroup D) (base u^ℤ_)
      isGroupʰ-u^ℤ base = record
        { preserves-ε = refl
        ; preserves-∙ = preserves-∙
        ; preserves-inverse = preserves-inverse
        }
        where
        preserves-∙ : (x y : ℤ) -> (base u^ℤ (x + y)) == (base u^ℤ x) u* (base u^ℤ y)
        preserves-∙ x y = u^ℤ-distrib-+ {base} {x} {y}
        preserves-inverse : (x : ℤ) -> (base u^ℤ (- x)) == (u1/ (base u^ℤ x))
        preserves-inverse x = u^ℤ-preserves-inverse {base} {x}

      u^ℤʰ : (base : Unit D) -> Groupʰ ℤ-Group (UnitGroup D)
      u^ℤʰ base = base u^ℤ_ , isGroupʰ-u^ℤ base
