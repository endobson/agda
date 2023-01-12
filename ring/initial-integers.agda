{-# OPTIONS --cubical --safe --exact-split #-}

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality
open import functions
open import int using (ℤ)
open import ring
open import funext
open import ring.implementations
open import semiring
open import sigma.base
open import truncation

module ring.initial-integers where

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {{R : Ring S AG}} where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S

  private
    lift-nat : Nat -> D
    lift-nat zero = 0#
    lift-nat (suc n) = (1# + (lift-nat n))

    lift-int : ℤ -> D
    lift-int (int.nonneg x) = lift-nat x
    lift-int (int.neg x) = - lift-nat (suc x)

    minus-lift-int : (x : ℤ) -> - (lift-int x) == lift-int (- x)
    minus-lift-int (int.zero-int) = minus-zero
    minus-lift-int (int.pos x) = refl
    minus-lift-int (int.neg x) = minus-double-inverse

    +-lift-nat : {x y : Nat} -> (lift-nat x) + (lift-nat y) == (lift-nat (x + y))
    +-lift-nat {zero} = +-left-zero
    +-lift-nat {suc n} =  +-assoc >=> (+-right (+-lift-nat {n}))

    +-lift-add1 : ∀ x -> (lift-int (int.add1 x)) == 1# + (lift-int x)
    +-lift-add1 (int.nonneg x) = refl
    +-lift-add1 (int.neg zero) = sym (+-right (cong -_ +-right-zero) >=> +-inverse)
    +-lift-add1 (int.neg (suc x)) = sym
      (begin
         1# + (lift-int (int.neg (suc x)))
       ==<>
         1# + - (1# + (lift-nat (suc x)))
       ==< +-right minus-distrib-plus >
         1# + (- 1# + - (lift-nat (suc x)))
       ==< sym +-assoc >
         (1# + - 1#) + - (lift-nat (suc x))
       ==< +-left +-inverse >
         0# + - (lift-nat (suc x))
       ==< +-left-zero >
         (lift-int (int.neg x))
       end)

    +-lift-sub1 : ∀ x -> (lift-int (int.sub1 x)) == - 1# + (lift-int x)
    +-lift-sub1 (int.neg x) = minus-distrib-plus
    +-lift-sub1 (int.nonneg zero) =
      sym( +-right-zero >=> cong -_ (sym +-right-zero))
    +-lift-sub1 (int.nonneg (suc x)) = sym
      (begin
         - 1# + (lift-int (int.nonneg (suc x)))
       ==<>
         - 1# + (1# + (lift-int (int.nonneg x)))
       ==< sym +-assoc >
         (- 1# + 1#) + (lift-int (int.nonneg x))
       ==< +-left +-commute >
         (1# + - 1#) + (lift-int (int.nonneg x))
       ==< +-left +-inverse >
         0# + (lift-int (int.nonneg x))
       ==< +-left-zero >
         (lift-int (int.nonneg x))
       end)

    +-lift-int : {x y : int.Int} -> (lift-int x) + (lift-int y) == (lift-int (x int.+ y))
    +-lift-int {int.nonneg zero} = +-left-zero >=> cong lift-int (sym int.+-left-zero)
    +-lift-int {int.nonneg (suc x)} {y} =
      +-assoc
      >=> +-right (+-lift-int {int.nonneg x} {y})
      >=> sym (+-lift-add1 ((int.nonneg x) int.+ y))
      >=> cong lift-int (sym int.add1-extract-left)
    +-lift-int {int.neg zero} {y} =
      +-left (cong -_ +-right-zero)
      >=> sym (+-lift-sub1 y)
      >=> cong (lift-int ∘ int.sub1) (sym int.+-left-zero)
      >=> cong lift-int (sym int.sub1-extract-left)
    +-lift-int {int.neg (suc x)} {y} =
      +-left minus-distrib-plus >=> +-assoc >=> +-right (+-lift-int {int.neg x} {y})
      >=> sym (+-lift-sub1 ((int.neg x) int.+ y))
      >=> cong lift-int (sym int.sub1-extract-left)

    *-lift-int : {x y : int.Int} -> (lift-int x) * (lift-int y) == (lift-int (x int.* y))
    *-lift-int {int.nonneg zero} = *-left-zero >=> cong lift-int (sym int.*-left-zero)
    *-lift-int {int.nonneg (suc x)} {y} =
      begin
        (lift-int (int.nonneg (suc x))) * (lift-int y)
      ==<>
        (1# + (lift-int (int.nonneg x))) * (lift-int y)
      ==< *-distrib-+-right >
        1# * (lift-int y) + (lift-int (int.nonneg x)) * (lift-int y)
      ==< +-left *-left-one >
        (lift-int y) + (lift-int (int.nonneg x)) * (lift-int y)
      ==< +-right (*-lift-int {int.nonneg x} {y}) >
        (lift-int y) + (lift-int ((int.nonneg x) int.* y))
      ==< +-lift-int {y} {(int.nonneg x) int.* y} >
        (lift-int (y int.+ (int.nonneg x) int.* y))
      ==< cong lift-int (sym int.add1-extract-*) >
        (lift-int (int.nonneg (suc x) int.* y))
      end
    *-lift-int {int.neg zero} {y} =
      begin
        (lift-int (int.neg zero)) * (lift-int y)
      ==<>
        - (1# + 0#) * (lift-int y)
      ==< *-left (cong -_ +-right-zero) >
       - 1# * (lift-int y)
      ==< *-left-minus-one >
        - (lift-int y)
      ==< (minus-lift-int y) >
        (lift-int (int.- y))
      ==< cong lift-int (cong int.-_ (sym (int.+-right-zero {y}))) >
        (lift-int (int.- (y int.+ int.zero-int)))
      ==< cong lift-int (cong int.-_ (int.+-right-zero {y}) >=> sym int.+-right-zero) >
        (lift-int ((int.- y) int.+ int.zero-int))
      ==< cong (\x -> (lift-int ((int.- y) int.+ x))) (sym (int.*-left-zero)) >
        (lift-int ((int.- y) int.+ (int.zero-int int.* y)))
      ==< cong lift-int (sym (int.sub1-extract-*)) >
        (lift-int ((int.neg zero) int.* y))
      end
    *-lift-int {int.neg (suc x)} {y} =
      begin
        (lift-int (int.neg (suc x))) * (lift-int y)
      ==<>
        - (1# + (lift-nat (suc x))) * (lift-int y)
      ==< *-left minus-distrib-plus >
       (- 1# + (lift-int (int.neg x))) * (lift-int y)
      ==< *-distrib-+-right >
        - 1# * (lift-int y) + (lift-int (int.neg x)) * (lift-int y)
      ==< +-left *-left-minus-one >
        - (lift-int y) + (lift-int (int.neg x)) * (lift-int y)
      ==< +-left (minus-lift-int y) >
        (lift-int (int.- y)) + (lift-int (int.neg x)) * (lift-int y)
      ==< +-right (*-lift-int {int.neg x} {y}) >
        (lift-int (int.- y)) + (lift-int ((int.neg x) int.* y))
      ==< +-lift-int {int.- y} {(int.neg x) int.* y} >
        (lift-int ((int.- y) int.+ (int.neg x) int.* y))
      ==< cong lift-int (sym int.sub1-extract-*) >
        (lift-int (int.neg (suc x) int.* y))
      end

    Ringʰ-lift-int : Ringʰ lift-int
    Ringʰ-lift-int = record
      { preserves-0# = refl
      ; preserves-1# = +-right-zero
      ; preserves-+ = \x y -> sym (+-lift-int {x} {y})
      ; preserves-* = \x y -> sym (*-lift-int {x} {y})
      ; preserves-minus = \x -> sym (minus-lift-int x)
      }



    module _ (f g : ℤ -> D) (fʰ : Ringʰ f) (gʰ : Ringʰ g) where
      private
        P : ℤ -> Type ℓD
        P x = f x == g x

        nat-case : (n : Nat) -> P (int.int n)
        nat-case zero =
          Ringʰ.preserves-0# fʰ >=>
          sym (Ringʰ.preserves-0# gʰ)
        nat-case (suc n) =
          cong f sn-path >=>
          Ringʰ.preserves-+ fʰ 1# (int.int n) >=>
          cong2 _+_ (Ringʰ.preserves-1# fʰ >=> sym (Ringʰ.preserves-1# gʰ))
                    (nat-case n) >=>
          sym (Ringʰ.preserves-+ gʰ 1# (int.int n)) >=>
          cong g (sym sn-path)

          where
          sn-path : (int.int (suc n)) == (1# + int.int n)
          sn-path = sym int.+-eval

        minus-case : (x : ℤ) -> P x -> P (- x)
        minus-case x fx=gx =
          Ringʰ.preserves-minus fʰ x >=>
          cong -_ fx=gx >=>
          sym (Ringʰ.preserves-minus gʰ x)

      unique-homo-path : f == g
      unique-homo-path = funExt (int.IntElim-ℕminus-elim nat-case minus-case)


  ∃!ℤ->Ring : ∃! (ℤ -> D) Ringʰ
  ∃!ℤ->Ring = (lift-int , Ringʰ-lift-int) ,
              \(f , fʰ) -> ΣProp-path isProp-Ringʰ (unique-homo-path _ f Ringʰ-lift-int fʰ)
