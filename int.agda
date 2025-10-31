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
open import int.base
open import int.multiplication
open import int.sign
open import monoid
open import nat
open import nat.order hiding (add1-<)
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

opaque
  *-NonZero-NonZero : {m n : Int} -> (NonZero m) -> (NonZero n) -> NonZero (m * n)
  *-NonZero-NonZero (inj-l p1) (inj-l p2) = inj-l (*-preserves-0< p1 p2)
  *-NonZero-NonZero (inj-l p1) (inj-r p2) = inj-r (*₁-preserves-<0 p1 p2)
  *-NonZero-NonZero (inj-r p1) (inj-l p2) = inj-r (*₂-preserves-<0 p1 p2)
  *-NonZero-NonZero (inj-r p1) (inj-r p2) = inj-l (*-flips-<0 p1 p2)

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
  *-isSign {pos-sign}  {pos-sign}          i1 i2 = *-preserves-0< i1 i2
  *-isSign {pos-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {pos-sign}  {neg-sign}          i1 i2 = *₁-preserves-<0 i1 i2
  *-isSign {zero-sign} {pos-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {zero-sign}         i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {neg-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {neg-sign}  {pos-sign}          i1 i2 = *₂-preserves-<0 i1 i2
  *-isSign {neg-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {neg-sign}  {neg-sign}          i1 i2 = *-flips-<0 i1 i2


  int->sign-preserves-* : {m n : Int} -> int->sign (m * n) == (int->sign m) s* (int->sign n)
  int->sign-preserves-* {m} {n} =
    isSign-unique (isSign-self (m * n))
      (*-isSign {int->sign m} {int->sign n} (isSign-self m) (isSign-self n))
