{-# OPTIONS --cubical --safe --exact-split #-}

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality
open import functions
open import int
open import ring
open import funext
open import ring.implementations.int
open import semiring
open import sigma.base
open import truncation

open EqReasoning

module ring.initial-integers where

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}}
         where
  private
    instance
      IACM = ACM

  private
    lift-nat : Nat -> D
    lift-nat zero = 0#
    lift-nat (suc n) = (1# + (lift-nat n))

    lift-int : ℤ -> D
    lift-int (nonneg x) = lift-nat x
    lift-int (neg x) = - lift-nat (suc x)

    minus-lift-int : (x : ℤ) -> - (lift-int x) == lift-int (- x)
    minus-lift-int (zero-int) = minus-zero
    minus-lift-int (pos x) = refl
    minus-lift-int (neg x) = minus-double-inverse

    +-lift-nat : {x y : Nat} -> (lift-nat x) + (lift-nat y) == (lift-nat (x + y))
    +-lift-nat {zero} = +-left-zero
    +-lift-nat {suc n} =  +-assoc >=> (+-right (+-lift-nat {n}))

    +-lift-add1 : ∀ x -> (lift-int (add1 x)) == 1# + (lift-int x)
    +-lift-add1 (nonneg x) = refl
    +-lift-add1 (neg zero) = sym (+-right (cong -_ +-right-zero) >=> +-inverse)
    +-lift-add1 (neg (suc x)) = sym
      (begin
         1# + (lift-int (neg (suc x)))
       ==<>
         1# + - (1# + (lift-nat (suc x)))
       ==< +-right minus-distrib-plus >
         1# + (- 1# + - (lift-nat (suc x)))
       ==< sym +-assoc >
         (1# + - 1#) + - (lift-nat (suc x))
       ==< +-left +-inverse >
         0# + - (lift-nat (suc x))
       ==< +-left-zero >
         (lift-int (neg x))
       end)

    +-lift-sub1 : ∀ x -> (lift-int (sub1 x)) == - 1# + (lift-int x)
    +-lift-sub1 (neg x) = minus-distrib-plus
    +-lift-sub1 (nonneg zero) =
      sym( +-right-zero >=> cong -_ (sym +-right-zero))
    +-lift-sub1 (nonneg (suc x)) = sym
      (begin
         - 1# + (lift-int (nonneg (suc x)))
       ==<>
         - 1# + (1# + (lift-int (nonneg x)))
       ==< sym +-assoc >
         (- 1# + 1#) + (lift-int (nonneg x))
       ==< +-left +-commute >
         (1# + - 1#) + (lift-int (nonneg x))
       ==< +-left +-inverse >
         0# + (lift-int (nonneg x))
       ==< +-left-zero >
         (lift-int (nonneg x))
       end)

    +-lift-int : {x y : Int} -> (lift-int x) + (lift-int y) == (lift-int (x + y))
    +-lift-int {nonneg zero} = +-left-zero >=> cong lift-int (sym +-left-zero)
    +-lift-int {nonneg (suc x)} {y} =
      +-assoc
      >=> +-right (+-lift-int {nonneg x} {y})
      >=> sym (+-lift-add1 ((nonneg x) + y))
      >=> cong lift-int (sym add1-extract-left)
    +-lift-int {neg zero} {y} =
      +-left (cong -_ +-right-zero)
      >=> sym (+-lift-sub1 y)
      >=> cong (lift-int ∘ sub1) (sym +-left-zero)
      >=> cong lift-int (sym sub1-extract-left)
    +-lift-int {neg (suc x)} {y} =
      +-left minus-distrib-plus >=> +-assoc >=> +-right (+-lift-int {neg x} {y})
      >=> sym (+-lift-sub1 ((neg x) + y))
      >=> cong lift-int (sym sub1-extract-left)

    *-lift-int : {x y : Int} -> (lift-int x) * (lift-int y) == (lift-int (x * y))
    *-lift-int {nonneg zero} = *-left-zero >=> cong lift-int (sym *-left-zero)
    *-lift-int {nonneg (suc x)} {y} =
      begin
        (lift-int (nonneg (suc x))) * (lift-int y)
      ==<>
        (1# + (lift-int (nonneg x))) * (lift-int y)
      ==< *-distrib-+-right >
        1# * (lift-int y) + (lift-int (nonneg x)) * (lift-int y)
      ==< +-left *-left-one >
        (lift-int y) + (lift-int (nonneg x)) * (lift-int y)
      ==< +-right (*-lift-int {nonneg x} {y}) >
        (lift-int y) + (lift-int ((nonneg x) * y))
      ==< +-lift-int {y} {(nonneg x) * y} >
        (lift-int (y + (nonneg x) * y))
      ==< cong lift-int (sym add1-extract-*) >
        (lift-int (nonneg (suc x) * y))
      end
    *-lift-int {neg zero} {y} =
      begin
        (lift-int (neg zero)) * (lift-int y)
      ==<>
        - (1# + 0#) * (lift-int y)
      ==< *-left (cong -_ +-right-zero) >
       - 1# * (lift-int y)
      ==< *-left-minus-one >
        - (lift-int y)
      ==< (minus-lift-int y) >
        (lift-int (- y))
      ==< cong lift-int (cong -_ (sym +-right-zero)) >
        (lift-int (- (y + zero-int)))
      ==< cong lift-int (cong -_ (ℤ+-right-zero {y}) >=> sym +-right-zero) >
        (lift-int ((- y) + zero-int))
      ==< cong (\x -> (lift-int ((- y) + x))) (sym (*-left-zero)) >
        (lift-int ((- y) + (zero-int * y)))
      ==< cong lift-int (sym (sub1-extract-*)) >
        (lift-int ((neg zero) * y))
      end
    *-lift-int {neg (suc x)} {y} =
      begin
        (lift-int (neg (suc x))) * (lift-int y)
      ==<>
        - (1# + (lift-nat (suc x))) * (lift-int y)
      ==< *-left minus-distrib-plus >
       (- 1# + (lift-int (neg x))) * (lift-int y)
      ==< *-distrib-+-right >
        - 1# * (lift-int y) + (lift-int (neg x)) * (lift-int y)
      ==< +-left *-left-minus-one >
        - (lift-int y) + (lift-int (neg x)) * (lift-int y)
      ==< +-left (minus-lift-int y) >
        (lift-int (- y)) + (lift-int (neg x)) * (lift-int y)
      ==< +-right (*-lift-int {neg x} {y}) >
        (lift-int (- y)) + (lift-int ((neg x) * y))
      ==< +-lift-int { - y} {(neg x) * y} >
        (lift-int ((- y) + (neg x) * y))
      ==< cong lift-int (sym sub1-extract-*) >
        (lift-int (neg (suc x) * y))
      end

    Ringʰ-lift-int : {{R : Ring S AG}} -> Ringʰ lift-int
    Ringʰ-lift-int = record
      { preserves-0# = refl
      ; preserves-1# = +-right-zero
      ; preserves-+ = \x y -> sym (+-lift-int {x} {y})
      ; preserves-* = \x y -> sym (*-lift-int {x} {y})
      ; preserves-minus = \x -> sym (minus-lift-int x)
      }



    module _ {{R : Ring S AG}} (f g : ℤ -> D) (fʰ : Ringʰ f) (gʰ : Ringʰ g) where
      private
        P : ℤ -> Type ℓD
        P x = f x == g x

        nat-case : (n : Nat) -> P (int n)
        nat-case zero =
          Ringʰ.preserves-0# fʰ >=>
          sym (Ringʰ.preserves-0# gʰ)
        nat-case (suc n) =
          cong f sn-path >=>
          Ringʰ.preserves-+ fʰ 1# (int n) >=>
          cong2 _+_ (Ringʰ.preserves-1# fʰ >=> sym (Ringʰ.preserves-1# gʰ))
                    (nat-case n) >=>
          sym (Ringʰ.preserves-+ gʰ 1# (int n)) >=>
          cong g (sym sn-path)

          where
          sn-path : (int (suc n)) == (1# + int n)
          sn-path = sym +-eval

        minus-case : (x : ℤ) -> P x -> P (- x)
        minus-case x fx=gx =
          Ringʰ.preserves-minus fʰ x >=>
          cong -_ fx=gx >=>
          sym (Ringʰ.preserves-minus gʰ x)

      unique-homo-path : f == g
      unique-homo-path = funExt (IntElim-ℕminus-elim nat-case minus-case)


  ∃!ℤ->Ring : {{R : Ring S AG}} -> ∃! (ℤ -> D) Ringʰ
  ∃!ℤ->Ring = (lift-int , Ringʰ-lift-int) ,
              \(f , fʰ) -> ΣProp-path isProp-Ringʰ (unique-homo-path _ f Ringʰ-lift-int fʰ)
