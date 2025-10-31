{-# OPTIONS --cubical --safe --exact-split #-}

module int where

open import additive-group
open import additive-group.instances.int
open import base
open import discrete
open import equality
open import hlevel
open import int.add1
open import int.addition
open import int.multiplication
open import monoid
open import nat
open import nat.order
open import order
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.instances.int
open import relation
open import ring.implementations.int
open import semiring
open import sign using (Sign ; s⁻¹_ ; _s*_ ; pos-sign ; zero-sign ; neg-sign )
open import sum

open import int.base public
open import int.cover public
open import int.sign public

open EqReasoning

opaque
  add1-NonNeg : {n : Int} -> (NonNeg n) -> (Pos (add1 n))
  add1-NonNeg (i , p) = (suc i , tt) , add1-extract-left >=> cong add1 p

  add1-Pos : {n : Int} -> (Pos n) -> (Pos (add1 n))
  add1-Pos p = add1-NonNeg (weaken-< p)

  sub1-NonPos : {n : Int} -> (NonPos n) -> (Neg (sub1 n))
  sub1-NonPos (i , p) = (suc i , tt) ,
    sub1-extract-right >=> sym sub1-extract-left >=> p

  sub1-Neg : {n : Int} -> (Neg n) -> (Neg (sub1 n))
  sub1-Neg n = sub1-NonPos (weaken-< n)

  +-Pos-NonNeg : {m n : Int} -> (Pos m) -> (NonNeg n) -> Pos (m + n)
  +-Pos-NonNeg 0<m 0≤n =
    trans-≤-< (trans-≤-= 0≤n (sym +-left-zero))
              (+₂-preserves-< 0<m)

  +-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m + n)
  +-Pos-Pos = +-preserves-0<

  +-Neg-Neg : {m n : Int} -> (Neg m) -> (Neg n) -> Neg (m + n)
  +-Neg-Neg = +-preserves-<0

  +-Neg-NonPos : {m n : Int} -> (Neg m) -> (NonPos n) -> Neg (m + n)
  +-Neg-NonPos m<0 n≤0 =
    trans-<-≤ (+₂-preserves-< m<0) (trans-=-≤ +-left-zero n≤0)


  *-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m * n)
  *-Pos-Pos = *-preserves-0<

  *-Pos-Neg : {m n : Int} -> (Pos m) -> (Neg n) -> Neg (m * n)
  *-Pos-Neg 0<m n<0 = trans-<-= (*₂-flips-< 0<m n<0) *-left-zero

  *-Neg-Pos : {m n : Int} -> (Neg m) -> (Pos n) -> Neg (m * n)
  *-Neg-Pos m<0 0<n = trans-<-= (*₁-flips-< m<0 0<n) *-right-zero

  *-Neg-Neg : {m n : Int} -> (Neg m) -> (Neg n) -> Pos (m * n)
  *-Neg-Neg = *-flips-<0

  *-NonZero-NonZero : {m n : Int} -> (NonZero m) -> (NonZero n) -> NonZero (m * n)
  *-NonZero-NonZero (inj-l p1) (inj-l p2) = inj-l (*-Pos-Pos p1 p2)
  *-NonZero-NonZero (inj-l p1) (inj-r p2) = inj-r (*-Pos-Neg p1 p2)
  *-NonZero-NonZero (inj-r p1) (inj-l p2) = inj-r (*-Neg-Pos p1 p2)
  *-NonZero-NonZero (inj-r p1) (inj-r p2) = inj-l (*-Neg-Neg p1 p2)


  *-NonPos-NonNeg : {m n : Int} -> (NonPos m) -> (NonNeg n) -> NonPos (m * n)
  *-NonPos-NonNeg m≤0 0≤n = trans-≤-= (*₁-flips-≤ m≤0 0≤n) *-right-zero

  *-NonNeg-NonPos : {m n : Int} -> (NonNeg m) -> (NonPos n) -> NonPos (m * n)
  *-NonNeg-NonPos 0≤m n≤0 = trans-≤-= (*₂-flips-≤ 0≤m n≤0) *-left-zero


  NonZero->!=0 : {x : Int} (nz-x : NonZero x) -> x != (int 0)
  NonZero->!=0 (inj-l 0<x) x=0 = irrefl-path-< (sym x=0) 0<x
  NonZero->!=0 (inj-r x<0) x=0 = irrefl-path-< x=0 x<0

  *-NonZero₁ : {m n : Int} -> NonZero (m * n) -> NonZero m
  *-NonZero₁ nz = ⊎-swap (proj₁ (*-reflects-<>0 (⊎-swap nz)))

  *-Zero₁ : {m n : Int} -> Zero m -> Zero (m * n)
  *-Zero₁ {zero-int} {n} _ = subst Zero (sym (*-left-zeroᵉ n)) tt
  *-Zero₂ : {m n : Int} -> Zero n -> Zero (m * n)
  *-Zero₂ {m} {zero-int} _ = subst Zero (sym (*-right-zeroᵉ m)) tt

  minus-isSign : {m : Int} {s : Sign} -> isSign s m -> isSign (s⁻¹ s) (- m)
  minus-isSign {m} {pos-sign} = minus-flips-0<
  minus-isSign {m} {neg-sign} = minus-flips-<0
  minus-isSign {zero-int} {zero-sign} _ = tt

  *-isSign : {s1 s2 : Sign} {m n : Int} -> isSign s1 m -> isSign s2 n -> isSign (s1 s* s2) (m * n)
  *-isSign {pos-sign}  {pos-sign}          i1 i2 = *-Pos-Pos i1 i2
  *-isSign {pos-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {pos-sign}  {neg-sign}          i1 i2 = *-Pos-Neg i1 i2
  *-isSign {zero-sign} {pos-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {zero-sign}         i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {neg-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {neg-sign}  {pos-sign}          i1 i2 = *-Neg-Pos i1 i2
  *-isSign {neg-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {neg-sign}  {neg-sign}          i1 i2 = *-Neg-Neg i1 i2


  int->sign-preserves-* : {m n : Int} -> int->sign (m * n) == (int->sign m) s* (int->sign n)
  int->sign-preserves-* {m} {n} =
    isSign-unique (isSign-self (m * n))
      (*-isSign {int->sign m} {int->sign n} (isSign-self m) (isSign-self n))
