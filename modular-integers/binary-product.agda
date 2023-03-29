{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers.binary-product where

open import abs
open import additive-group hiding (0#)
open import additive-group.instances.int
open import base
open import div
open import equality
open import equivalence
open import fin
open import gcd.euclidean-algorithm
open import hlevel
open import int
open import isomorphism
open import linear-combo
open import modular-integers
open import nat
open import prime-gcd
open import relatively-prime
open import ring
open import ring.implementations.int
open import semiring hiding (1#)
open import set-quotient
open import sigma


--shrink*-z* : (n : Nat) (n2⁺ : Nat⁺) -> ℤ/nℤ ( n *' ⟨ n2⁺ ⟩) -> ℤ/nℤ n
--shrink*-z* n n2⁺@(n2 , pos-n2) = ℤ/nℤElim.rec isSet-ℤ/nℤ val handle
--  where
--  val : ℤ -> ℤ/nℤ n
--  val x = [ (quotient x n2⁺) ]
--  handle : (z1 z2 : ℤ) (r : CongruentMod (n *' n2) z1 z2) -> Path (ℤ/nℤ n) (val z1) (val z2)
--  handle z1 z2 (congruent-mod (d , p)) = eq/ _ _ (congruent-mod n%)
--    where
--    m1 = int n
--    m2 = int n2
--    module qr1 = QuotientRemainder (quotient-remainder n2⁺ z1)
--    module qr2 = QuotientRemainder (quotient-remainder n2⁺ z2)
--
--    m2%0 : m2 div (z1 + - z2)
--    m2%0 = d * m1 , *-assoc >=> *-right (sym int-inject-*') >=> p
--
--    c2 : CongruentMod n2 z1 z2
--    c2 = congruent-mod m2%0
--
--    r-path : qr1.r == qr2.r
--    r-path = repr~ n2⁺ _ _ c2
--    r-path2 : (qr1.ri + - qr2.ri) == (int 0)
--    r-path2 = +-left (cong (\x -> int ⟨ x ⟩) r-path) >=> add-minus-zero
--
--    path1 : z1 + - z2 == (qr1.q + (- qr2.q)) * m2
--    path1 =
--      begin
--        z1 + - z2
--      ==< cong2 (\x y -> x + - y) (sym qr1.path) (sym qr2.path) >
--        (qr1.q * m2 + qr1.ri) + - (qr2.q * m2 + qr2.ri)
--      ==< +-right minus-distrib-+ >
--        (qr1.q * m2 + qr1.ri) + (- (qr2.q * m2) + - qr2.ri)
--      ==< +-assoc >=> +-right (sym +-assoc >=> +-left +-commute >=> +-assoc) >=> sym +-assoc >
--        (qr1.q * m2 + - (qr2.q * m2)) + (qr1.ri + - qr2.ri)
--      ==< +-left (+-right (sym minus-extract-left)) >
--        (qr1.q * m2 + (- qr2.q) * m2) + (qr1.ri + - qr2.ri)
--      ==< +-left (sym *-distrib-+) >
--        (qr1.q + (- qr2.q)) * m2 + (qr1.ri + - qr2.ri)
--      ==< +-right r-path2 >=> +-right-zero >
--        (qr1.q + (- qr2.q)) * m2
--      end
--
--    path2 : (d * m1) * m2 == (qr1.q + (- qr2.q)) * m2
--    path2 = snd m2%0 >=> path1
--
--    path3 : (d * m1) == (qr1.q + (- qr2.q))
--    path3 = *-right-injective (Pos->NonZero (Pos'->Pos pos-n2)) path2
--
--    n% : m1 div (qr1.q + - qr2.q)
--    n% = d , path3



  --  cong f (repr~ n⁺ z1 z2 (congruent-mod n%))
  --  where
  --  f : Fin n -> ℤ/nℤ n
  --  f x = [ int ⟨ x ⟩ ]
  --  n% : (int n) div (z1 + - z2)
  --  n% = d * (int n2) , *-assoc >=> *-right (*-commute >=> sym int-inject-*') >=> p


module ℤ/nℤ×Elim {n1 : Nat} {n2 : Nat} where
  private
    variable
      ℓ : Level
      A : Type ℓ
      B : ℤ/nℤ n1 -> ℤ/nℤ n2 -> Type ℓ

  elimProp : (isPropB : (x : ℤ/nℤ n1) -> (y : ℤ/nℤ n2) -> isProp (B x y)) ->
             (f : (x y : ℤ) -> B [ x ] [ y ]) ->
             (x : ℤ/nℤ n1) -> (y : ℤ/nℤ n2) -> (B x y)
  elimProp isPropB f =
    ℤ/nℤElim.elimProp
      (\x -> isPropΠ (\y -> isPropB x y))
      (\x -> ℤ/nℤElim.elimProp (\y -> isPropB [ x ] y) (\y -> (f x y)))

private
  UnitRec : {ℓ : Level} {P : Type ℓ} {n : Nat} (isPropP : isProp P) (x : ℤ/nℤ n) ->
            ((y : ℤ) -> (x z* [ y ] == 1#) -> P) -> (Unit x) -> P
  UnitRec {P = P} isPropP x f (y , path) =
    ℤ/nℤElim.elimProp {C = \y -> x z* y == 1# -> P}
                      (\_ -> isPropΠ (\_ -> isPropP)) f y path





module _ {n1 : Nat} {n2 : Nat} (rp : RelativelyPrime⁰ n1 n2) where
  private
    m1 = int n1
    m2 = int n2

    lc : LinearCombination (int n1) (int n2) (int 1)
    lc = gcd'->linear-combo (relatively-prime->gcd rp)
    module lc = LinearCombination lc


  lift*-z*₁ : ℤ/nℤ n1 -> ℤ/nℤ (n1 *' n2)
  lift*-z*₁ = ℤ/nℤElim.rec isSet-ℤ/nℤ (\x -> [ lc.y * (x * (int n2)) ]) handle
    where
    handle : (z1 z2 : ℤ) (r : CongruentMod n1 z1 z2) ->
             [ lc.y * (z1 * (int n2)) ] == [ lc.y * (z2 * (int n2)) ]
    handle z1 z2 (congruent-mod (d , p)) = eq/ _ _ (congruent-mod n%)
      where
      n% : (int (n1 *' n2)) div (lc.y * (z1 * (int n2)) + - (lc.y * (z2 * (int n2))))
      n% = lc.y * d ,
           (*-right int-inject-*' >=> *-assoc >=> *-right (sym *-assoc >=> *-left p)) >=>
           *-right (*-distrib-+-right >=> +-right minus-extract-left) >=>
           (*-distrib-+-left >=> +-right minus-extract-right)

  lift*-z*₂ : ℤ/nℤ n2 -> ℤ/nℤ (n1 *' n2)
  lift*-z*₂ = ℤ/nℤElim.rec isSet-ℤ/nℤ (\x -> [ lc.x * (x * (int n1)) ]) handle
    where
    handle : (z1 z2 : ℤ) (r : CongruentMod n2 z1 z2) ->
             [ lc.x * (z1 * (int n1)) ] == [ lc.x * (z2 * (int n1)) ]
    handle z1 z2 (congruent-mod (d , p)) = eq/ _ _ (congruent-mod n%)
      where
      n% : (int (n1 *' n2)) div (lc.x * (z1 * (int n1)) + - (lc.x * (z2 * (int n1))))
      n% = lc.x * d ,
           (*-right (int-inject-*' >=> *-commute) >=> *-assoc >=> *-right (sym *-assoc >=> *-left p)) >=>
           *-right (*-distrib-+-right >=> +-right minus-extract-left) >=>
           (*-distrib-+-left >=> +-right minus-extract-right)

  private
    z*2 : ℤ/nℤ n1 -> ℤ/nℤ n2 -> ℤ/nℤ (n1 *' n2)
    z*2 x1 x2 = (lift*-z*₂ x2) z+ (lift*-z*₁ x1)

    z*2-inv₁ : ℤ/nℤ (n1 *' n2) -> ℤ/nℤ n1
    z*2-inv₁ = ℤ/nℤElim.rec isSet-ℤ/nℤ (\x -> [ x ]) handle
      where
      handle : (x y : ℤ) -> (CongruentMod (n1 *' n2) x y) -> [ x ] == [ y ]
      handle x y c@(congruent-mod (d , p)) = eq/ _ _ (congruent-mod n1%)
        where
        n1% : m1 div (x + - y)
        n1% = (d * m2) ,
              *-assoc >=> *-right (*-commute >=> sym int-inject-*') >=> p

    z*2-inv₂ : ℤ/nℤ (n1 *' n2) -> ℤ/nℤ n2
    z*2-inv₂ = ℤ/nℤElim.rec isSet-ℤ/nℤ (\x -> [ x ]) handle
      where
      handle : (x y : ℤ) -> (CongruentMod (n1 *' n2) x y) -> [ x ] == [ y ]
      handle x y c@(congruent-mod (d , p)) = eq/ _ _ (congruent-mod n2%)
        where
        n2% : m2 div (x + - y)
        n2% = (d * m1) , (*-assoc >=> *-right (sym int-inject-*') >=> p)


    z*2-inv-path1 : (x : ℤ/nℤ (n1 *' n2)) -> z*2 (z*2-inv₁ x) (z*2-inv₂ x) == x
    z*2-inv-path1 = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
      where
      handle : (x : ℤ) -> [ lc.x * (x * m1) + lc.y * (x * m2) ] == [ x ]
      handle x = cong [_] path
        where
        path : lc.x * (x * m1) + lc.y * (x * m2) == x
        path = cong2 _+_ (sym *-assoc >=> *-left *-commute >=> *-assoc >=> *-commute)
                         (sym *-assoc >=> *-left *-commute >=> *-assoc >=> *-commute) >=>
               sym *-distrib-+-right >=> *-left lc.path >=> *-left-one

    z*2-inv-path2 : (x : ℤ) (y : ℤ/nℤ n2) -> (z*2-inv₂ (z*2 [ x ] y)) == y
    z*2-inv-path2 x = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
      where
      handle : (y : ℤ) -> [ lc.x * (y * m1) + lc.y * (x * m2) ] == [ y ]
      handle y = eq/ _ _ (congruent-mod m2%diff)
        where
        path1 : lc.x * (y * m1) == y + (- y * lc.y * m2)
        path1 = sym +-right-zero >=> +-right (sym add-minus-zero) >=>
                +-left (sym *-assoc >=> *-left *-commute >=> *-assoc) >=>
                sym +-assoc >=> +-left (sym *-distrib-+-left >=> *-right lc.path >=> *-right-one) >=>
                +-right (sym minus-extract-left >=> sym *-assoc)

        path : lc.x * (y * m1) + lc.y * (x * m2) == y + ((- y * lc.y) + (lc.y * x)) * m2
        path = +-left path1 >=> +-right (sym *-assoc) >=>
               +-assoc >=> +-right (sym *-distrib-+-right)

        path2 : lc.x * (y * m1) + lc.y * (x * m2) + - y == ((- y * lc.y) + (lc.y * x)) * m2
        path2 = +-left (path >=> +-commute) >=> +-assoc >=> +-right add-minus-zero >=> +-right-zero

        m2%diff : m2 div ((lc.x * (y * m1) + lc.y * (x * m2)) + - y)
        m2%diff = ((- y * lc.y) + (lc.y * x)) , sym path2

    z*2-inv-path2-full : (x : ℤ/nℤ n1) (y : ℤ/nℤ n2) -> (z*2-inv₂ (z*2 x y)) == y
    z*2-inv-path2-full =
      ℤ/nℤElim.elimProp (\_ -> (isPropΠ (\_ -> isSet-ℤ/nℤ _ _))) z*2-inv-path2

    z*2-inv-path3 : (y : ℤ) (x : ℤ/nℤ n1) -> (z*2-inv₁ (z*2 x [ y ])) == x
    z*2-inv-path3 y = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
      where
      handle : (x : ℤ) -> [ lc.x * (y * m1) + lc.y * (x * m2) ] == [ x ]
      handle x = eq/ _ _ (congruent-mod m1%diff)
        where
        path1 : lc.y * (x * m2) == x + (- x * lc.x) * m1
        path1 = sym *-assoc >=> *-left *-commute >=> *-assoc >=>
                *-right (sym +-left-zero >=> +-left (sym add-minus-zero >=> +-commute) >=>
                         +-assoc >=> +-commute >=> +-left lc.path) >=>
                *-distrib-+-left >=> +-left *-right-one >=>
                +-right (minus-extract-right >=> sym minus-extract-left >=> sym *-assoc)


        path : lc.x * (y * m1) + lc.y * (x * m2) == x + ((- x * lc.x) + (lc.x * y)) * m1
        path = +-right path1 >=> +-commute >=> +-assoc >=>
               +-right (+-right (sym *-assoc) >=> sym *-distrib-+-right)

        path2 : (lc.x * (y * m1) + lc.y * (x * m2)) + - x == ((- x * lc.x) + (lc.x * y)) * m1
        path2 = +-left (path >=> +-commute) >=> +-assoc >=> +-right add-minus-zero >=> +-right-zero

        m1%diff : m1 div ((lc.x * (y * m1) + lc.y * (x * m2)) + - x)
        m1%diff = ((- x * lc.x) + (lc.x * y)) , sym path2

    z*2-inv-path3-full : (y : ℤ/nℤ n2) (x : ℤ/nℤ n1) -> (z*2-inv₁ (z*2 x y)) == x
    z*2-inv-path3-full =
      ℤ/nℤElim.elimProp (\_ -> (isPropΠ (\_ -> isSet-ℤ/nℤ _ _))) z*2-inv-path3

    ℤ/nℤ-×-eq : (ℤ/nℤ n1 × ℤ/nℤ n2) ≃ ℤ/nℤ (n1 *' n2)
    ℤ/nℤ-×-eq = isoToEquiv i
      where
      open Iso
      i : Iso (ℤ/nℤ n1 × ℤ/nℤ n2) (ℤ/nℤ (n1 *' n2))
      i .fun (x , y) = z*2 x y
      i .inv x .fst = z*2-inv₁ x
      i .inv x .snd = z*2-inv₂ x
      i .rightInv x = z*2-inv-path1 x
      i .leftInv (x , y) i = (z*2-inv-path3-full y x i) , (z*2-inv-path2-full x y i)


    z*2-distrib-*' : (x1 x2 : ℤ) (y1 y2 : ℤ) ->
                     (z*2 ([ x1 ] z* [ x2 ]) ([ y1 ] z* [ y2 ])) ==
                     ((z*2 [ x1 ] [ y1 ]) z* (z*2 [ x2 ] [ y2 ]))
    z*2-distrib-*' x1 x2 y1 y2 = eq/ _ _ (congruent-mod n%)
      where
      t1 = lc.x * (y1 * y2 * m1)
      t2 = lc.y * (x1 * x2 * m2)
      t3 = (lc.x * (y1 * m1) + lc.y * (x1 * m2))
      t4 = (lc.x * (y2 * m1) + lc.y * (x2 * m2))

      t5 = (lc.x * (y1 * m1)) * (lc.x * (y2 * m1))
      t6 = (lc.y * (x1 * m2)) * (lc.x * (y2 * m1))
      t7 = (lc.x * (y1 * m1)) * (lc.y * (x2 * m2))
      t8 = (lc.y * (x1 * m2)) * (lc.y * (x2 * m2))

      p1 : t3 * t4 == (t5 + t6) + (t7 + t8)
      p1 = *-distrib-+-left >=> cong2 _+_ *-distrib-+-right *-distrib-+-right

      t5-2 = t1 * (lc.x * m1)
      pt5-2 : t5 == t5-2
      pt5-2 = *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc >=>
              *-left (*-assoc >=> *-right (*-assoc >=> *-right *-commute >=> sym *-assoc))

      p2 : (int 1 + - (lc.x * m1)) == (lc.y * m2)
      p2 = +-left (sym lc.path >=> +-commute) >=> +-assoc >=> +-right add-minus-zero >=> +-right-zero

      p3 : t1 + - t5 == ((lc.x * (y1 * y2)) * lc.y) * (m1 * m2)
      p3 = +-left (sym *-right-one) >=> +-right (cong -_ pt5-2 >=> sym minus-extract-right) >=>
           sym *-distrib-+-left >=> *-right p2 >=>
           *-left (sym *-assoc) >=> *-assoc >=>
           *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=>
           sym *-assoc

      d1 : (int (n1 *' n2)) div (t1 + - t5)
      d1 = ((lc.x * (y1 * y2)) * lc.y) , *-right int-inject-*' >=> sym p3


      t8-2 = t2 * (lc.y * m2)
      pt8-2 : t8 == t8-2
      pt8-2 = *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc >=>
              *-left (*-assoc >=> *-right (*-assoc >=> *-right *-commute >=> sym *-assoc))

      p4 : (int 1 + - (lc.y * m2)) == (lc.x * m1)
      p4 = +-left (sym lc.path) >=> +-assoc >=> +-right add-minus-zero >=> +-right-zero

      p5 : t2 + - t8 == ((lc.y * (x1 * x2)) * lc.x) * (m1 * m2)
      p5 = +-left (sym *-right-one) >=> +-right (cong -_ pt8-2 >=> sym minus-extract-right) >=>
           sym *-distrib-+-left >=> *-right p4 >=>
           *-left (sym *-assoc) >=> *-assoc >=>
           *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=>
           sym *-assoc >=> *-right *-commute

      d2 : (int (n1 *' n2)) div (t2 + - t8)
      d2 = ((lc.y * (x1 * x2)) * lc.x) , *-right int-inject-*' >=> sym p5

      p6 : t6 == ((lc.y * x1) * (lc.x * y2)) * (m1 * m2)
      p6 = *-left (sym *-assoc) >=> *-assoc >=>
           *-right (*-commute >=> *-left (sym *-assoc) >=> *-assoc) >=> sym *-assoc

      p7 : t7 == ((lc.x * y1) * (lc.y * x2)) * (m1 * m2)
      p7 = *-left (sym *-assoc) >=> *-assoc >=>
           *-right (*-commute >=> *-left (sym *-assoc) >=> *-assoc) >=> sym *-assoc >=>
           *-right *-commute

      d3 : (int (n1 *' n2)) div t6
      d3 = ((lc.y * x1) * (lc.x * y2)) , *-right int-inject-*' >=> sym p6
      d4 : (int (n1 *' n2)) div t7
      d4 = ((lc.x * y1) * (lc.y * x2)) , *-right int-inject-*' >=> sym p7

      d5 : int (n1 *' n2) div ((t1 + - t5) + (t2 + - t8) + - t6 + - t7)
      d5 = div-sum (div-sum (div-sum d1 d2) (div-negate d3)) (div-negate d4)

      p8 : ((t1 + - t5) + (t2 + - t8) + - t6 + - t7) == (t1 + t2 + - (t3 * t4))
      p8 =
        begin
          ((t1 + - t5) + (t2 + - t8) + - t6 + - t7)
        ==< +-left (+-left (+-assoc >=> +-right (sym +-assoc >=> +-left +-commute >=> +-assoc))) >
          (t1 + (t2 + (- t5 + - t8)) + - t6 + - t7)
        ==< +-left (+-left (sym +-assoc)) >
          ((t1 + t2) + (- t5 + - t8)) + - t6 + - t7
        ==< +-left +-assoc >=> +-assoc >
          (t1 + t2) + (((- t5 + - t8) + - t6) + - t7)
        ==< +-right (+-left (+-left (sym minus-distrib-+) >=> sym minus-distrib-+) >=>
                     sym minus-distrib-+) >
          (t1 + t2) + - (((t5 + t8) + t6) + t7)
        ==< +-right (cong -_ (+-left (+-assoc >=> +-right +-commute >=> sym +-assoc))) >
          (t1 + t2) + - (((t5 + t6) + t8) + t7)
        ==< +-right (cong -_ (+-assoc >=> +-right +-commute)) >
          (t1 + t2) + - ((t5 + t6) + (t7 + t8))
        ==< +-right (cong -_ (sym p1)) >
          (t1 + t2) + - (t3 * t4)
        end

      n% : int (n1 *' n2) div (t1 + t2 + - (t3 * t4))
      n% = fst d5 , snd d5 >=> p8


    z*2-distrib-* : (x1 x2 : ℤ/nℤ n1) (y1 y2 : ℤ/nℤ n2) ->
                    (z*2 (x1 z* x2) (y1 z* y2)) == ((z*2 x1 y1) z* (z*2 x2 y2))
    z*2-distrib-* =
      ℤ/nℤElim.elimProp2
        (\ _ _ -> isPropΠ2 (\_ _ -> isSet-ℤ/nℤ _ _))
        (\ x1 x2 -> ℤ/nℤElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _)
                                       (\ y1 y2 -> (z*2-distrib-*' x1 x2 y1 y2)))




  module _ where

    unit-forward : (x : ℤ/nℤ n1) (y : ℤ/nℤ n2) -> Unit' x -> Unit' y -> Unit' (z*2 x y)
    unit-forward x y ux uy =
      unit' _ (z*2 xi yi) (sym (z*2-distrib-* x xi y yi) >=> cong2 z*2 xp yp >=>
                           cong [_] (cong2 _+_ (*-right *-left-one) (*-right *-left-one) >=> lc.path))
      where
      xi = Unit'.inv ux
      xp = Unit'.path ux
      yi = Unit'.inv uy
      yp = Unit'.path uy

    unit-backward₁ : (x : ℤ/nℤ n1) (y : ℤ/nℤ n2) -> Unit' (z*2 x y) -> Unit' x
    unit-backward₁ x y u = unit' _ (z*2-inv₁ xyi) (sym p3)
      where
      xyi = Unit'.inv u
      p = Unit'.path u
      xi = (z*2-inv₁ xyi)
      yi = (z*2-inv₂ xyi)

      p2 : 1# == z*2 (x z* xi) (y z* yi)
      p2 = sym p >=> cong ((z*2 x y) z*_) (sym (z*2-inv-path1 xyi)) >=>
           sym (z*2-distrib-* x xi y yi)

      p3 : 1# == (x z* xi)
      p3 = cong z*2-inv₁ p2 >=> z*2-inv-path3-full (y z* yi) (x z* xi)


    unit-backward₂ : (x : ℤ/nℤ n1) (y : ℤ/nℤ n2) -> Unit' (z*2 x y) -> Unit' y
    unit-backward₂ x y u = unit' _ (z*2-inv₂ xyi) (sym p3)
      where
      xyi = Unit'.inv u
      p = Unit'.path u
      xi = (z*2-inv₁ xyi)
      yi = (z*2-inv₂ xyi)

      p2 : 1# == z*2 (x z* xi) (y z* yi)
      p2 = sym p >=> cong ((z*2 x y) z*_) (sym (z*2-inv-path1 xyi)) >=>
           sym (z*2-distrib-* x xi y yi)

      p3 : 1# == (y z* yi)
      p3 = cong z*2-inv₂ p2 >=> z*2-inv-path2-full (x z* xi) (y z* yi)



    ℤ/nℤ*-×-eq'-3 : (x : ℤ/nℤ n1) (y : ℤ/nℤ n2) -> ((Unit' x × Unit' y) ≃ (Unit' (z*2 x y)))
    ℤ/nℤ*-×-eq'-3 x y = isoToEquiv i
      where
      open Iso
      i : Iso (Unit' x × Unit' y) (Unit' (z*2 x y))
      i .fun (ux , uy) = unit-forward x y ux uy
      i .inv u = unit-backward₁ x y u , unit-backward₂ x y u
      i .rightInv _ = isProp-Unit' {x = (z*2 x y)} _ _
      i .leftInv _ = (isProp× (isProp-Unit' {x = x}) (isProp-Unit' {x = y})) _ _



    ℤ/nℤ*-×-eq'-1 : (Σ[ ( x , y) ∈ (ℤ/nℤ n1 × ℤ/nℤ n2) ] (Unit' x × Unit' y))
                    ≃ (Σ[ ( x , y) ∈ (ℤ/nℤ n1 × ℤ/nℤ n2) ] (Unit' (z*2 x y)))
    ℤ/nℤ*-×-eq'-1 = existential-eq (\(x , y) -> ℤ/nℤ*-×-eq'-3 x y)


    ℤ/nℤ*-×-eq'-2 : (ℤ/nℤ* n1 × ℤ/nℤ* n2) ≃
                    (Σ[ ( x , y) ∈ (ℤ/nℤ n1 × ℤ/nℤ n2) ] (Unit' x × Unit' y))
    ℤ/nℤ*-×-eq'-2 = isoToEquiv i
      where
      open Iso
      i : Iso (ℤ/nℤ* n1 × ℤ/nℤ* n2) (Σ[ ( x , y) ∈ (ℤ/nℤ n1 × ℤ/nℤ n2) ] (Unit' x × Unit' y))
      i .fun ((x , ux) , (y , uy)) = (x , y) , (ux , uy)
      i .inv ((x , y) , (ux , uy)) = (x , ux) , (y , uy)
      i .rightInv _ = refl
      i .leftInv _ = refl



  ℤ/nℤ*-×-eq : (ℤ/nℤ* n1 × ℤ/nℤ* n2) ≃ ℤ/nℤ* (n1 *' n2)
  ℤ/nℤ*-×-eq = ℤ/nℤ*-×-eq'-2 >eq> ℤ/nℤ*-×-eq'-1 >eq> (equiv⁻¹ (reindexΣ ℤ/nℤ-×-eq Unit'))


-- module _ {n1 : Nat} (n2⁺ : Nat⁺) (rp : RelativelyPrime⁰ n1 ⟨ n2⁺ ⟩) where
--   private
--     n2 = ⟨ n2⁺ ⟩
--
--   shrink-lift : (x : ℤ/nℤ n1) -> shrink*-z* n1 n2⁺ (lift*-z* n2 x) == x
--   shrink-lift = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
--     where
--     handle : (x : ℤ) -> [ (quotient (x * (int n2)) n2⁺) ] == [ x ]
--     handle x = cong [_] (cong QuotientRemainder.q (isContr-QuotientRemainder .snd qr))
--       where
--       zero-<⁺ : (n : Nat⁺) -> 0 < ⟨ n ⟩
--       zero-<⁺ (suc _ , _) = zero-<
--       zero-fin⁺ : (n : Nat⁺) -> Fin ⟨ n ⟩
--       zero-fin⁺ n = 0 , zero-<⁺ n
--
--       qr : QuotientRemainder n2⁺ (x * (int n2))
--       qr = record { q = x ; r = (zero-fin⁺ n2⁺) ; path = +-right-zero }
