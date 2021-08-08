{-# OPTIONS --cubical --safe --exact-split #-}

module order where

open import base
open import equality
open import hlevel
open import relation
open import truncation

private
  variable
    ℓD ℓ< : Level

record LinearOrderStr (D : Type ℓD) (ℓ< : Level) : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
  field
    _<_ : D -> D -> Type ℓ<
    isProp-< : (x y : D) -> isProp (x < y)
    irrefl-< : Irreflexive _<_
    trans-< : Transitive _<_
    comparison-< : Comparison _<_
    connected-< : Connected _<_

  _>_ : D -> D -> Type ℓ<
  x > y = y < x

  _≮_ : D -> D -> Type ℓ<
  x ≮ y = ¬ (x < y)

  _≯_ : D -> D -> Type ℓ<
  x ≯ y = ¬ (x > y)

  asym-< : Asymmetric _<_
  asym-< x<y y<x = irrefl-< (trans-< x<y y<x)


module _ {D : Type ℓD} {{S : LinearOrderStr D ℓ<}} where
  open LinearOrderStr S public

  abstract
    trans-≮ : Transitive _≮_
    trans-≮ {a} {b} {c} a≮b b≮c a<c = unsquash isPropBot (∥-map handle (comparison-< a b c a<c))
      where
      handle : (a < b) ⊎ (b < c) -> Bot
      handle (inj-l a<b) = a≮b a<b
      handle (inj-r b<c) = b≮c b<c

    <->!= : {d1 d2 : D} -> d1 < d2 -> d1 != d2
    <->!= {d1} {d2} d1<d2 d1=d2 = irrefl-< (subst (_< d2) d1=d2 d1<d2)

    =->≮ : {d1 d2 : D} -> d1 == d2 -> d1 ≮ d2
    =->≮ {d1} {d2} d1=d2 = subst (d1 ≮_) d1=d2 irrefl-<


record TotalOrderStr (D : Type ℓD) (ℓ≤ : Level) : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
  field
    _≤_ : D -> D -> Type ℓ≤
    isProp-≤ : (x y : D) -> isProp (x ≤ y)
    refl-≤ : Reflexive _≤_
    trans-≤ : Transitive _≤_
    antisym-≤ : Antisymmetric _≤_
    connex-≤ : Connex _≤_

  _≥_ : D -> D -> Type ℓ≤
  x ≥ y = y ≤ x

module _ {D : Type ℓD} {{S : TotalOrderStr D ℓ<}} where
  open TotalOrderStr S public


  abstract
    =->≤ : {d1 d2 : D} -> d1 == d2 -> d1 ≤ d2
    =->≤ {d1} {d2} d1=d2 = subst (d1 ≤_) d1=d2 refl-≤

module _ (D : Type ℓD) (ℓ< ℓ≤ : Level)
         (<-Str : LinearOrderStr D ℓ<)
         (≤-Str : TotalOrderStr D ℓ≤) where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  record CompatibleOrderStr : Type (ℓ-max (ℓ-max ℓ≤ ℓ<) ℓD) where
    field
      weaken-< : {d1 d2 : D} -> d1 < d2 -> d1 ≤ d2
      strengthen-≤-≠ : {d1 d2 : D} -> d1 ≤ d2 -> d1 != d2 -> d1 < d2

module _ {D : Type ℓD} {ℓ< ℓ≤ : Level} {<-Str : LinearOrderStr D ℓ<} {≤-Str : TotalOrderStr D ℓ≤}
         {{S : CompatibleOrderStr D ℓ< ℓ≤ <-Str ≤-Str}} where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  open CompatibleOrderStr S public

  abstract
    strengthen-≤-≮ : {d1 d2 : D} -> d1 ≤ d2 -> d1 ≮ d2 -> d1 == d2
    strengthen-≤-≮ {d1} {d2} d1≤d2 d1≮d2 = connected-< d1≮d2 d2≮d1
      where
      d2≮d1 : d2 ≮ d1
      d2≮d1 d2<d1 = irrefl-< (subst (_< d1) d2=d1 d2<d1)
        where
        d2=d1 : d2 == d1
        d2=d1 = antisym-≤ (weaken-< d2<d1) d1≤d2

    trans-<-≤ : {d1 d2 d3 : D} -> d1 < d2 -> d2 ≤ d3 -> d1 < d3
    trans-<-≤ {d1} {d2} {d3} d1<d2 d2≤d3 =
      strengthen-≤-≠ (trans-≤ (weaken-< d1<d2) d2≤d3) d1!=d3
      where
      d2!=d1 : d2 != d1
      d2!=d1 d2=d1 = <->!= d1<d2 (sym d2=d1)

      d1!=d3 : d1 != d3
      d1!=d3 d1=d3 = asym-< d1<d2 (strengthen-≤-≠ d2≤d1 d2!=d1)
        where
        d2≤d1 : d2 ≤ d1
        d2≤d1 = subst (d2 ≤_) (sym d1=d3) d2≤d3

    trans-≤-< : {d1 d2 d3 : D} -> d1 ≤ d2 -> d2 < d3 -> d1 < d3
    trans-≤-< {d1} {d2} {d3} d1≤d2 d2<d3 =
      strengthen-≤-≠ (trans-≤ d1≤d2 (weaken-< d2<d3)) d1!=d3
      where
      d3!=d2 : d3 != d2
      d3!=d2 d3=d2 = <->!= d2<d3 (sym d3=d2)

      d1!=d3 : d1 != d3
      d1!=d3 d1=d3 = asym-< d2<d3 (strengthen-≤-≠ d3≤d2 d3!=d2)
        where
        d3≤d2 : d3 ≤ d2
        d3≤d2 = subst (_≤ d2) d1=d3 d1≤d2


module _ {D : Type ℓD} {ℓ< : Level} (<-Str : LinearOrderStr D ℓ<) where
  private
    instance
      <-Str-I = <-Str

  record DecidableLinearOrderStr : Type (ℓ-max ℓ< ℓD) where
    field
      trichotomous-< : Trichotomous _<_

module _ {D : Type ℓD} {ℓ< : Level} {<-Str : LinearOrderStr D ℓ<}
         {{S : DecidableLinearOrderStr <-Str}} where
  open DecidableLinearOrderStr S public

module _ {D : Type ℓD} {ℓ< ℓ≤ : Level} {<-Str : LinearOrderStr D ℓ<} {≤-Str : TotalOrderStr D ℓ≤}
         {{S : CompatibleOrderStr D ℓ< ℓ≤ <-Str ≤-Str}} {{DS : DecidableLinearOrderStr <-Str}} where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str
      IS = S
      IDS = DS

  abstract
    split-< : (d1 d2 : D) -> (d1 < d2) ⊎ (d2 ≤ d1)
    split-< d1 d2 = handle (trichotomous-< d1 d2)
      where
      handle : Tri (d1 < d2) (d1 == d2) (d2 < d1) -> (d1 < d2) ⊎ (d2 ≤ d1)
      handle (tri< d1<d2 _ _) = inj-l d1<d2
      handle (tri= _ d1=d2 _) = inj-r (subst (_≤ d1) d1=d2 refl-≤)
      handle (tri> _ _ d2<d1) = inj-r (weaken-< d2<d1)

    decide-< : (d1 d2 : D) -> Dec (d1 < d2)
    decide-< d1 d2 = handle (trichotomous-< d1 d2)
      where
      handle : Tri (d1 < d2) (d1 == d2) (d2 < d1) -> Dec (d1 < d2)
      handle (tri< d1<d2 _ _) = yes d1<d2
      handle (tri= d1≮d2 _ _) = no d1≮d2
      handle (tri> d1≮d2 _ _) = no d1≮d2
