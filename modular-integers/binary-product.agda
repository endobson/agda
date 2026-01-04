{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers.binary-product where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.modular-integers
open import additive-group.instances.nat
open import base
open import div
open import equality-path
open import equivalence
open import gcd.euclidean-algorithm
open import hlevel.base
open import int.base
open import int.nat
open import isomorphism
open import linear-combo
open import modular-integers
open import nat
open import prime-gcd
open import relatively-prime
open import ring
open import ring.implementations.int
open import semiring
open import semiring.instances.modular-integers
open import semiring.instances.nat
open import semiring.unit
open import set-quotient


module _ {n₁ : Nat} {n₂ : Nat} (rp : RelativelyPrime⁰ n₁ n₂) where

  private
    n₁₂ : Nat
    n₁₂ = n₁ * n₂
    m₁ m₂ m₁₂ : Int
    m₁ = int n₁
    m₂ = int n₂
    m₁₂ = int n₁₂
    lc : LinearCombination m₁ m₂ (int 1)
    lc = gcd'->linear-combo (relatively-prime->gcd rp)
    module lc = LinearCombination lc

    lift₁-z* : ℤ/nℤ n₁ -> ℤ/nℤ n₁₂
    lift₁-z* = SetQuotientElim.rec isSet-ℤ/nℤ (\x -> [ lc.y * (x * m₂) ]) f~
      where
      opaque
        f~ : (z₁ z₂ : ℤ) (r : ℤ/nℤ~ n₁ z₁ z₂) ->
             Path (ℤ/nℤ n₁₂) [ lc.y * (z₁ * m₂) ] [ lc.y * (z₂ * m₂) ]
        f~ z₁ z₂ (d , p) = eq/ _ _ m%
          where
          m% : m₁₂ div (diff (lc.y * (z₁ * m₂)) (lc.y * (z₂ * m₂)))
          m% = lc.y * d ,
            (*-right ℕ->ℤ-* >=> *-assoc >=> *-right (sym *-assoc >=> *-left p)) >=>
            *-right (*-distrib-+-right >=> +-right minus-extract-left) >=>
            (*-distrib-+-left >=> +-right minus-extract-right)

    lift₂-z* : ℤ/nℤ n₂ -> ℤ/nℤ n₁₂
    lift₂-z* = SetQuotientElim.rec isSet-ℤ/nℤ (\x -> [ lc.x * (x * m₁) ]) f~
      where
      opaque
        f~ : (z₁ z₂ : ℤ) (r : ℤ/nℤ~ n₂ z₁ z₂) ->
             Path (ℤ/nℤ n₁₂) [ lc.x * (z₁ * m₁) ] [ lc.x * (z₂ * m₁) ]
        f~ z₁ z₂ (d , p) = eq/ _ _ m%
          where
          m% : m₁₂ div (diff (lc.x * (z₁ * m₁)) (lc.x * (z₂ * m₁)))
          m% = lc.x * d ,
            (*-right (ℕ->ℤ-* >=> *-commute) >=> *-assoc >=> *-right (sym *-assoc >=> *-left p)) >=>
            *-right (*-distrib-+-right >=> +-right minus-extract-left) >=>
            (*-distrib-+-left >=> +-right minus-extract-right)

    z* : ℤ/nℤ n₁ -> ℤ/nℤ n₂ -> ℤ/nℤ (n₁ * n₂)
    z* x₁ x₂ = (lift₁-z* x₁) + (lift₂-z* x₂)


    z*-inv₁ : ℤ/nℤ n₁₂ -> ℤ/nℤ n₁
    z*-inv₁ = SetQuotientElim.rec isSet-ℤ/nℤ (\x -> [ x ]) handle
      where
      opaque
        handle : (x y : ℤ) -> ℤ/nℤ~ n₁₂ x y -> Path (ℤ/nℤ n₁) [ x ] [ y ]
        handle x y (d , p) = eq/ _ _ m₁%
          where
          m₁% : m₁ div (diff x y)
          m₁% = (d * m₂) ,
                *-assoc >=> *-right (*-commute >=> sym ℕ->ℤ-*) >=> p

    z*-inv₂ : ℤ/nℤ n₁₂ -> ℤ/nℤ n₂
    z*-inv₂ = SetQuotientElim.rec isSet-ℤ/nℤ (\x -> [ x ]) handle
      where
      opaque
        handle : (x y : ℤ) -> ℤ/nℤ~ n₁₂ x y -> Path (ℤ/nℤ n₂) [ x ] [ y ]
        handle x y (d , p) = eq/ _ _ m₂%
          where
          m₂% : m₂ div (diff x y)
          m₂% = (d * m₁) ,
                *-assoc >=> *-right (sym ℕ->ℤ-*) >=> p

    opaque
      z*-path₁ : (x : ℤ/nℤ n₁) (y : ℤ/nℤ n₂) -> (z*-inv₁ (z* x y)) == x
      z*-path₁ = SetQuotientElim.elimProp (\_ -> isPropΠ \_ -> isSet-ℤ/nℤ _ _) z*-path₁'
        where
        z*-path₁' : (x : ℤ) (y : ℤ/nℤ n₂) -> (z*-inv₁ (z* [ x ] y)) == [ x ]
        z*-path₁' x = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
          where
          handle : (y : ℤ) -> Path (ℤ/nℤ n₁) [ lc.y * (x * m₂) + lc.x * (y * m₁) ] [ x ]
          handle y = eq/ _ _ m₁%diff
            where
            path₁ : 1# + (- (lc.y * m₂)) == (lc.x * m₁)
            path₁ = +-left (sym lc.path >=> +-commute) >=> +-assoc >=> diff-step

            path₂ : x + (- (lc.y * (x * m₂))) == (x * lc.x) * m₁
            path₂ =
              +-cong (sym *-left-one) (cong -_ (*-right *-commute >=> sym *-assoc) >=> sym minus-extract-left) >=>
              sym *-distrib-+-right >=>
              *-left path₁ >=>
              *-commute >=> sym *-assoc

            m₁%diff : m₁ div (diff (lc.y * (x * m₂) + lc.x * (y * m₁)) x)
            m₁%diff = diff (lc.x * y) (x * lc.x)  ,
              *-distrib-diff-right >=>
              +-cong (sym path₂) (cong -_ *-assoc) >=>
              +-assoc >=>
              +-right (sym minus-distrib-plus)

      z*-path₂ : (x : ℤ/nℤ n₁) (y : ℤ/nℤ n₂) -> (z*-inv₂ (z* x y)) == y
      z*-path₂ = SetQuotientElim.elimProp (\_ -> isPropΠ \_ -> isSet-ℤ/nℤ _ _) z*-path₂'
        where
        z*-path₂' : (x : ℤ) (y : ℤ/nℤ n₂) -> (z*-inv₂ (z* [ x ] y)) == y
        z*-path₂' x = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
          where
          handle : (y : ℤ) -> Path (ℤ/nℤ n₂) [ lc.y * (x * m₂) + lc.x * (y * m₁) ] [ y ]
          handle y = eq/ _ _ m₂%diff
            where
            path₁ : 1# + (- (lc.x * m₁)) == (lc.y * m₂)
            path₁ = +-left (sym lc.path) >=> +-assoc >=> diff-step

            path₂ : y + (- (lc.x * (y * m₁))) == (y * lc.y) * m₂
            path₂ =
              +-cong (sym *-left-one) (cong -_ (*-right *-commute >=> sym *-assoc) >=> sym minus-extract-left) >=>
              sym *-distrib-+-right >=>
              *-left path₁ >=>
              *-commute >=> sym *-assoc

            m₂%diff : m₂ div (diff (lc.y * (x * m₂) + lc.x * (y * m₁)) y)
            m₂%diff = diff (lc.y * x) (y * lc.y) ,
              *-distrib-diff-right >=>
              +-cong (sym path₂) (cong -_ *-assoc) >=>
              +-assoc >=>
              +-right (+-commute >=> sym minus-distrib-plus)

      z*-path₃ : (x : ℤ/nℤ n₁₂) -> z* (z*-inv₁ x) (z*-inv₂ x) == x
      z*-path₃ = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
        where
        handle : (x : ℤ) -> Path (ℤ/nℤ n₁₂) [ lc.y * (x * m₂) + lc.x * (x * m₁) ] [ x ]
        handle x = cong [_] path
          where
          path : lc.y * (x * m₂) + lc.x * (x * m₁) == x
          path = cong2 _+_ (*-right *-commute >=> sym *-assoc) (*-right *-commute >=> sym *-assoc) >=>
                 +-commute >=> sym *-distrib-+-right >=> *-left lc.path >=> *-left-one

  ℤ/nℤ-×-eq : (ℤ/nℤ n₁ × ℤ/nℤ n₂) ≃ ℤ/nℤ n₁₂
  ℤ/nℤ-×-eq = isoToEquiv i
    where
    open Iso
    i : Iso (ℤ/nℤ n₁ × ℤ/nℤ n₂) (ℤ/nℤ n₁₂)
    i .fun (x , y) = z* x y
    i .inv x .fst = z*-inv₁ x
    i .inv x .snd = z*-inv₂ x
    i .rightInv x = z*-path₃ x
    i .leftInv (x , y) i = (z*-path₁ x y i) , (z*-path₂ x y i)


  private
    opaque
      z*-distrib-*' : (x₁ x₂ : ℤ) (y₁ y₂ : ℤ) ->
                      (z* ([ x₁ ] * [ x₂ ]) ([ y₁ ] * [ y₂ ])) ==
                      ((z* [ x₁ ] [ y₁ ]) * (z* [ x₂ ] [ y₂ ]))
      z*-distrib-*' x₁ x₂ y₁ y₂ =
        sym (eqSec ℤ/nℤ-×-eq l) ∙∙
        (\i -> z* (path₁ i) (path₂ i)) ∙∙
        (eqSec ℤ/nℤ-×-eq r)
        where
        l : ℤ/nℤ n₁₂
        l = (z* ([ x₁ ] * [ x₂ ]) ([ y₁ ] * [ y₂ ]))
        r : ℤ/nℤ n₁₂
        r = (z* [ x₁ ] [ y₁ ]) * (z* [ x₂ ] [ y₂ ])

        path₁ : z*-inv₁ l == z*-inv₁ r
        path₁ = z*-path₁ [ x₁ * x₂ ] [ y₁ * y₂ ] >=>
                sym (*-cong (z*-path₁ [ x₁ ] [ y₁ ]) (z*-path₁ [ x₂ ] [ y₂ ]))
        path₂ : z*-inv₂ l == z*-inv₂ r
        path₂ = z*-path₂ [ x₁ * x₂ ] [ y₁ * y₂ ] >=>
                sym (*-cong (z*-path₂ [ x₁ ] [ y₁ ]) (z*-path₂ [ x₂ ] [ y₂ ]))

      z*-distrib-* : (x₁ x₂ : ℤ/nℤ n₁) (y₁ y₂ : ℤ/nℤ n₂) ->
                     (z* (x₁ * x₂) (y₁ * y₂)) == ((z* x₁ y₁) * (z* x₂ y₂))
      z*-distrib-* =
        SetQuotientElim.elimProp2
          (\ _ _ -> isPropΠ2 (\_ _ -> isSet-ℤ/nℤ _ _))
          (\ x₁ x₂ -> SetQuotientElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _)
                                                (\ y₁ y₂ -> (z*-distrib-*' x₁ x₂ y₁ y₂)))

      z*-inv₁-distrib-* : (x y : ℤ/nℤ n₁₂) -> z*-inv₁ (x * y) == z*-inv₁ x * z*-inv₁ y
      z*-inv₁-distrib-* = SetQuotientElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> refl)
      z*-inv₂-distrib-* : (x y : ℤ/nℤ n₁₂) -> z*-inv₂ (x * y) == z*-inv₂ x * z*-inv₂ y
      z*-inv₂-distrib-* = SetQuotientElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> refl)


  ℤ/nℤˣ-×-eq : (ℤ/nℤˣ n₁ × ℤ/nℤˣ n₂) ≃ ℤ/nℤˣ n₁₂
  ℤ/nℤˣ-×-eq = isoToEquiv i
    where
    open Iso

    isUnit-forward : (x : ℤ/nℤ n₁) (y : ℤ/nℤ n₂) -> isUnit x -> isUnit y -> isUnit (z* x y)
    isUnit-forward x y (is-unit xi xp) (is-unit yi yp) = is-unit (z* xi yi) xyp
      where
      opaque
        xyp : (z* x y) * (z* xi yi) == 1#
        xyp = (sym (z*-distrib-* x xi y yi) >=> cong2 z* xp yp >=>
               cong [_] (cong2 _+_ (*-right *-left-one) (*-right *-left-one) >=>
                         +-commute >=> lc.path))

    isUnit-backward : (xy : ℤ/nℤ n₁₂) -> isUnit xy -> isUnit (z*-inv₁ xy) × isUnit (z*-inv₂ xy)
    isUnit-backward xy (is-unit xyi p) = is-unit (z*-inv₁ xyi) q₁ , is-unit (z*-inv₂ xyi) q₂
      where
      x xi : ℤ/nℤ n₁
      x  = z*-inv₁ xy
      xi = z*-inv₁ xyi
      y yi : ℤ/nℤ n₂
      y  = z*-inv₂ xy
      yi = z*-inv₂ xyi
      opaque
        q₁ : x * xi == 1#
        q₁ = sym (z*-inv₁-distrib-* xy xyi) >=> cong z*-inv₁ p
        q₂ : y * yi == 1#
        q₂ = sym (z*-inv₂-distrib-* xy xyi) >=> cong z*-inv₂ p

    i : Iso (ℤ/nℤˣ n₁ × ℤ/nℤˣ n₂) (ℤ/nℤˣ n₁₂)
    i .fun ((x , ux) , (y , uy)) = z* x y , isUnit-forward x y ux uy
    i .inv (x , ux) = (z*-inv₁ x , proj₁ (isUnit-backward x ux)) ,
                      (z*-inv₂ x , proj₂ (isUnit-backward x ux))
    i .rightInv (x , _) = unit-path (z*-path₃ x)
    i .leftInv ((x , _) , (y , _)) = cong2 _,_ (unit-path (z*-path₁ x y)) (unit-path (z*-path₂ x y))
