{-# OPTIONS --cubical --safe --exact-split #-}

module ring.exponentiation where

open import additive-group
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import group
open import group.int
open import int using (ℤ)
open import monoid
open import nat
open import ring
open import semiring
open import sigma.base

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {{R : Ring S AG}} where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
    module R = Ring R
    Unit = R.Unit
    1u = R.1u
    _u*_ = R._u*_
    u1/_ = R.u1/_

  private
    _^ℕ_ : D -> ℕ -> D
    x ^ℕ zero = 1#
    x ^ℕ (suc n) = x * (x ^ℕ n)

    ^ℕ-one : {x : D} -> (x ^ℕ 1) == x
    ^ℕ-one = *-right-one

    _u^ℕ_ : Unit -> ℕ -> Unit
    a u^ℕ zero = 1u
    a u^ℕ (suc n) = a u* (a u^ℕ n)


    u^ℕ-one : {x : Unit} -> (x u^ℕ 1) == x
    u^ℕ-one = ΣProp-path R.isProp-isUnit *-right-one

    u^ℕ-distrib-+ : {b : Unit} {x y : ℕ} -> b u^ℕ (x + y) == (b u^ℕ x) u* (b u^ℕ y)
    u^ℕ-distrib-+ {b} {zero} {y} =
      cong (b u^ℕ_) +-left-zero >=> sym (Monoid.∙-left-ε R.Monoid-u*)
    u^ℕ-distrib-+ {b} {suc x} {y} =
      cong (b u*_) (u^ℕ-distrib-+ {b} {x} {y}) >=> sym (Monoid.∙-assoc R.Monoid-u*)


  _u^ℤ_ : Unit -> ℤ -> Unit
  a u^ℤ (int.nonneg n) = a u^ℕ n
  a u^ℤ (int.neg n) = u1/ (a u^ℕ (suc n))

  private
    u^ℤ-add1 : (u : Unit) (x : ℤ) -> u u^ℤ (int.add1 x) == u u* (u u^ℤ x)
    u^ℤ-add1 u (int.nonneg n) = refl
    u^ℤ-add1 u@(u' , is-u)  (int.neg zero) = path
      where
      module m = CommMonoid R.CommMonoid-u*
      module is-u = R.isUnit is-u

      path : 1u == u u* (u1/ (u u^ℕ (suc zero)))
      path = ΣProp-path R.isProp-isUnit (sym is-u.path) >=> (cong (\x -> (u u* (u1/ x))) (sym u^ℕ-one))
    u^ℤ-add1 u (int.neg (suc n)) = sym path
      where
      path : u u* (u1/ (u u* (u u^ℕ (suc n)))) == (u1/ (u u^ℕ (suc n)))
      path =
        cong (u u*_) (R.u1/-distrib-u*)
        >=> sym (Monoid.∙-assoc R.Monoid-u*)
        >=> cong (_u* (u1/ (u u^ℕ (suc n)))) R.u1/-right-inverse
        >=> Monoid.∙-left-ε R.Monoid-u*

  u^ℤ-sub1 : (u : Unit) (x : ℤ) -> u u^ℤ (int.sub1 x) == (u1/ u) u* (u u^ℤ x)
  u^ℤ-sub1 u (int.nonneg zero) = ΣProp-path R.isProp-isUnit refl
  u^ℤ-sub1 u (int.nonneg (suc n)) =
    sym (Monoid.∙-left-ε R.Monoid-u*) >=>
    cong (_u* (u u^ℤ (int.int n))) (sym (R.u1/-left-inverse {u})) >=>
    (Monoid.∙-assoc R.Monoid-u*)
  u^ℤ-sub1 u (int.neg n) =
    cong u1/_ (u^ℤ-add1 u (int.int (suc n))) >=> R.u1/-distrib-u*

  private
    u^ℤ-preserves-inverse : {b : Unit} {x : ℤ} -> (b u^ℤ (int.- x)) == u1/ (b u^ℤ x)
    u^ℤ-preserves-inverse {x = int.zero-int} = ΣProp-path R.isProp-isUnit refl
    u^ℤ-preserves-inverse {x = int.pos x} = refl
    u^ℤ-preserves-inverse {x = int.neg x} = ΣProp-path R.isProp-isUnit refl

    u^ℤ-distrib-+-NonNeg : {b : Unit} {x y : ℤ} -> int.NonNeg x ->
                           b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)
    u^ℤ-distrib-+-NonNeg {b} {int.zero-int} _ =
      cong (b u^ℤ_) int.+-left-zero >=> sym (Monoid.∙-left-ε R.Monoid-u*)
    u^ℤ-distrib-+-NonNeg {b} {int.nonneg (suc x)} {y} _ =
      cong (b u^ℤ_) int.add1-extract-left
      >=> u^ℤ-add1 b ((int.int x) int.+ y)
      >=> cong (b u*_) (u^ℤ-distrib-+-NonNeg {b} {int.nonneg x} {y} (int.NonNeg-nonneg x))
      >=> sym (Monoid.∙-assoc R.Monoid-u*)
      >=> cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b (int.int x)))
    u^ℤ-distrib-+-NonNeg {b} {int.neg x} (inj-l ())
    u^ℤ-distrib-+-NonNeg {b} {int.neg x} (inj-r ())

    u^ℤ-distrib-+ : {b : Unit} {x y : ℤ} -> b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)
    u^ℤ-distrib-+ {b} {x} {y} = int.IntElim-add1sub1-elim z add1-case sub1-case x
      where
      P : ℤ -> Type ℓD
      P x = b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)

      z : P (int.int 0)
      z = cong (b u^ℤ_) (int.+-left-zero) >=> sym (Monoid.∙-left-ε R.Monoid-u*)
      add1-case : (x : ℤ) -> (P x) -> (P (int.add1 x))
      add1-case x p =
        cong (b u^ℤ_) (int.add1-extract-left) >=>
        u^ℤ-add1 b (x int.+ y) >=> cong (b u*_) p >=>
        sym (Monoid.∙-assoc R.Monoid-u*) >=>
        cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b x))

      sub1-case : (x : ℤ) -> (P x) -> (P (int.sub1 x))
      sub1-case x p =
        cong (b u^ℤ_) (int.sub1-extract-left) >=>
        u^ℤ-sub1 b (x int.+ y) >=> cong ((u1/ b) u*_) p >=>
        sym (Monoid.∙-assoc R.Monoid-u*) >=>
        cong (_u* (b u^ℤ y)) (sym (u^ℤ-sub1 b x))

    Groupʰ-u^ℤ : (base : Unit) -> Groupʰᵉ GroupStr-ℤ+ R.GroupStr-u* (base u^ℤ_)
    Groupʰ-u^ℤ base = record
      { preserves-ε = refl
      ; preserves-∙ = preserves-∙
      ; preserves-inverse = preserves-inverse
      }
      where
      preserves-∙ : (x y : ℤ) -> (base u^ℤ (x int.+ y)) == (base u^ℤ x) u* (base u^ℤ y)
      preserves-∙ x y = u^ℤ-distrib-+ {base} {x} {y}
      preserves-inverse : (x : ℤ) -> (base u^ℤ (int.- x)) == (u1/ (base u^ℤ x))
      preserves-inverse x = u^ℤ-preserves-inverse {base} {x}
