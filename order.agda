{-# OPTIONS --cubical --safe --exact-split #-}

module order where

open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import functions
open import hlevel
open import hlevel.hedberg
open import relation
open import sum
open import truncation

open import order.partial-order public

private
  variable
    ℓD ℓ< ℓ≤ ℓ# : Level

record isLinearOrder {D : Type ℓD} (_<_ : Rel D ℓ<)  : Type (ℓ-max ℓ< ℓD) where
  no-eta-equality
  pattern
  field
    isProp-< : {x y : D} -> isProp (x < y)
    irrefl-< : Irreflexive _<_
    trans-< : Transitive _<_
    comparison-< : Comparison _<_
    connected-< : Connected _<_


  asym-< : Asymmetric _<_
  asym-< x<y y<x = irrefl-< (trans-< x<y y<x)

  irrefl-path-< : IrreflexivePath _<_
  irrefl-path-< = Irreflexive->IrreflexivePath _<_ irrefl-<

  isSet-D : isSet D
  isSet-D = Stable==->isSet Stable==
    where
    Stable== : (x y : D) -> Stable (x == y)
    Stable== x y ¬¬x=y = connected-< (\x<y -> ¬¬x=y (\x=y -> irrefl-path-< x=y x<y))
                                     (\y<x -> ¬¬x=y (\x=y -> irrefl-path-< (sym x=y) y<x))

isProp-isLinearOrder : {D : Type ℓD} (_<_ : Rel D ℓ<) -> isProp (isLinearOrder _<_)
isProp-isLinearOrder _ O1@(record {}) O2@(record {}) = \i -> record
  { isProp-< = isProp-isProp O1.isProp-< O2.isProp-< i
  ; irrefl-< = isProp¬ O1.irrefl-< O2.irrefl-<  i
  ; trans-< = isPropΠ2 (\_ _ -> O1.isProp-<) O1.trans-< O2.trans-< i
  ; comparison-< = isPropΠ4 (\_ _ _ _ -> squash) O1.comparison-< O2.comparison-< i
  ; connected-< = isPropΠ2 (\_ _ -> O1.isSet-D _ _) O1.connected-< O2.connected-< i
  }
  where
  module O1 = isLinearOrder O1
  module O2 = isLinearOrder O2


record LinearOrderStr (D : Type ℓD) (ℓ< : Level) : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
  no-eta-equality
  pattern
  field
    _<_ : D -> D -> Type ℓ<
    isLinearOrder-< : isLinearOrder _<_

  open module isLinearOrder-< = isLinearOrder isLinearOrder-< public

module _ {D : Type ℓD} {lt : Rel D ℓ<} {{S : isLinearOrder lt}} where
  open isLinearOrder S public hiding
    (  isSet-D
    )

  _<_ : D -> D -> Type ℓ<
  x < y = lt x y

  _>_ : D -> D -> Type ℓ<
  x > y = y < x

  _≮_ : D -> D -> Type ℓ<
  x ≮ y = ¬ (x < y)

  _≯_ : D -> D -> Type ℓ<
  x ≯ y = ¬ (x > y)

  abstract
    trans-≮ : Transitive _≮_
    trans-≮ {a} {b} {c} a≮b b≮c a<c = unsquash isPropBot (∥-map handle (comparison-< a b c a<c))
      where
      handle : (a < b) ⊎ (b < c) -> Bot
      handle (inj-l a<b) = a≮b a<b
      handle (inj-r b<c) = b≮c b<c

    trans-<-= : {d1 d2 d3 : D} -> d1 < d2 -> d2 == d3 -> d1 < d3
    trans-<-= {d1 = d1} d1<d2 d2=d3 = subst (d1 <_) d2=d3 d1<d2

    trans-=-< : {d1 d2 d3 : D} -> d1 == d2 -> d2 < d3 -> d1 < d3
    trans-=-< {d3 = d3} d1=d2 d2<d3 = subst (_< d3) (sym d1=d2) d2<d3

    <->!= : {d1 d2 : D} -> d1 < d2 -> d1 != d2
    <->!= {d1} {d2} d1<d2 d1=d2 = irrefl-< (subst (_< d2) d1=d2 d1<d2)

    =->≮ : {d1 d2 : D} -> d1 == d2 -> d1 ≮ d2
    =->≮ {d1} {d2} d1=d2 = subst (d1 ≮_) d1=d2 irrefl-<

  _<>_ : Rel D ℓ<
  a <> b = (a < b) ⊎ (b < a)

  isProp-<> : {a b : D} -> isProp (a <> b)
  isProp-<> (inj-l lt1) (inj-l lt2) = cong inj-l (isProp-< lt1 lt2)
  isProp-<> (inj-l lt1) (inj-r gt2) = bot-elim (asym-< lt1 gt2)
  isProp-<> (inj-r gt1) (inj-l lt2) = bot-elim (asym-< gt1 lt2)
  isProp-<> (inj-r gt1) (inj-r gt2) = cong inj-r (isProp-< gt1 gt2)

  Tri< : (x y : D) -> Type (ℓ-max ℓD ℓ<)
  Tri< x y = Tri (x < y) (x == y) (y < x)

  tri<' : {x y : D} -> x < y -> Tri< x y
  tri<' x<y = tri< x<y (\p -> irrefl-path-< p x<y) (asym-< x<y)

  tri>' : {x y : D} -> x > y -> Tri< x y
  tri>' x>y = tri> (asym-< x>y) (\p -> irrefl-path-< (sym p) x>y) x>y

  tri=' : {x y : D} -> x == y -> Tri< x y
  tri=' x=y = tri= (irrefl-path-< x=y) x=y (irrefl-path-< (sym x=y))

  isProp-Tri< : {x y : D} -> isProp (Tri< x y)
  isProp-Tri< = isProp-Tri isProp-< (isLinearOrder.isSet-D useⁱ _ _) isProp-<


module _ {D : Type ℓD} {D# : Rel D ℓ#} {D< : Rel D ℓ<}
         (A : isTightApartness D#) (O : isLinearOrder D<) where
  private
    instance
     IO = O
     IA = A

  record ApartLinearOrderStr : Type (ℓ-max* 3 ℓ# ℓ< ℓD) where
    no-eta-equality
    field
      <>-equiv-# : {a b : D} -> (a <> b) ≃ (a # b)


module _ {D : Type ℓD} {D# : Rel D ℓ#} {D< : Rel D ℓ<}
         {A : isTightApartness D#} {O : isLinearOrder D<}
         {{AO : ApartLinearOrderStr A O}} where
  open ApartLinearOrderStr AO public

module _ {D : Type ℓD} {D< : Rel D ℓ<} (L : isLinearOrder D<) where
  private
    instance
      IL = L

    tight-<> : Tight _<>_
    tight-<> ¬<> =
      connected-< (¬<> ∘ inj-l) (¬<> ∘ inj-r)

    irrefl-<> : Irreflexive _<>_
    irrefl-<> = either irrefl-< irrefl-<

    sym-<> : Symmetric _<>_
    sym-<> = ⊎-swap

    comparison-<> : Comparison _<>_
    comparison-<> x y z =
      either (∥-map (⊎-map inj-l inj-l) ∘ comparison-< x y z)
             (∥-map (⊎-swap ∘ ⊎-map inj-r inj-r) ∘ comparison-< z y x)

  isLinearOrder->isTightApartness-<> : isTightApartness _<>_
  isLinearOrder->isTightApartness-<> = record
    { tight-# = tight-<>
    ; irrefl-# = irrefl-<>
    ; sym-# = sym-<>
    ; comparison-# = comparison-<>
    ; isProp-# = isProp-<>
    }

  TrivialApartLinearOrderStr : ApartLinearOrderStr isLinearOrder->isTightApartness-<> IL
  TrivialApartLinearOrderStr = record
    { <>-equiv-# = idEquiv _
    }

module _ {D : Type ℓD} {le : Rel D ℓ≤} {{S : isPartialOrder le}} where
  open isPartialOrder S public hiding
    ( isSet-D
    )

  _≤_ : Rel D ℓ≤
  _≤_ = le

  abstract
    path-≤ : {d1 d2 : D} -> d1 == d2 -> d1 ≤ d2
    path-≤ {d1} {d2} d1=d2 = subst (d1 ≤_) d1=d2 refl-≤

    trans-≤-= : {d1 d2 d3 : D} -> d1 ≤ d2 -> d2 == d3 -> d1 ≤ d3
    trans-≤-= {d1 = d1} d1≤d2 d2=d3 = subst (d1 ≤_) d2=d3 d1≤d2

    trans-=-≤ : {d1 d2 d3 : D} -> d1 == d2 -> d2 ≤ d3 -> d1 ≤ d3
    trans-=-≤ {d3 = d3} d1=d2 d2≤d3 = subst (_≤ d3) (sym d1=d2) d2≤d3

    refl-≤ᵉ : (d : D) -> d ≤ d
    refl-≤ᵉ _ = refl-≤




module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} (PO : isPartialOrder D≤) where
  private
    instance
      IPO = PO

  record TotalOrderStr : Type (ℓ-max ℓD ℓ≤) where
    no-eta-equality
    field
      connex-≤ : Connex _≤_


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {P : isPartialOrder D≤} {{T : TotalOrderStr P}} where
  open TotalOrderStr T public

module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         (<-Str : isLinearOrder D<)
         (≤-Str : isPartialOrder D≤) where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-I = ≤-Str

  record CompatibleOrderStr : Type (ℓ-max (ℓ-max ℓ≤ ℓ<) ℓD) where
    no-eta-equality
    field
      convert-≮ : {d1 d2 : D} -> d1 ≮ d2 -> d2 ≤ d1


module _ {D : Type ℓD} {D< : Rel D ℓ<} (L : isLinearOrder D<) where
  private
    instance
      IL = L

  isLinearOrder->isPartialOrder-≯ : isPartialOrder _≯_
  isLinearOrder->isPartialOrder-≯ = record
    { refl-≤ = irrefl-<
    ; trans-≤ = \a≤b b≤c -> trans-≮ b≤c a≤b
    ; antisym-≤ = \a≤b b≤a -> connected-< b≤a a≤b
    ; isProp-≤ = isProp¬
    }

  CompatibleNegatedLinearOrder : CompatibleOrderStr L isLinearOrder->isPartialOrder-≯
  CompatibleNegatedLinearOrder = record
    { convert-≮ = \x -> x
    }


module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {<-Str : isLinearOrder D<} {≤-Str : isPartialOrder D≤}
         {{S : CompatibleOrderStr <-Str ≤-Str}} where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  open CompatibleOrderStr S public

  weaken-< : {d1 d2 : D} -> d1 < d2 -> d1 ≤ d2
  weaken-< d1<d2 = convert-≮ (asym-< d1<d2)

  abstract
    strengthen-≤-≮ : {d1 d2 : D} -> d1 ≤ d2 -> d1 ≮ d2 -> d1 == d2
    strengthen-≤-≮ {d1} {d2} d1≤d2 d1≮d2 = antisym-≤ d1≤d2 (convert-≮ d1≮d2)

    trans-<-≤ : {d1 d2 d3 : D} -> d1 < d2 -> d2 ≤ d3 -> d1 < d3
    trans-<-≤ {d1} {d2} {d3} d1<d2 d2≤d3 =
      unsquash isProp-< (∥-map handle (comparison-< d1 d3 d2 d1<d2))
      where
      handle : (d1 < d3 ⊎ d3 < d2) -> d1 < d3
      handle (inj-l d1<d3) = d1<d3
      handle (inj-r d3<d2) = bot-elim (<->!= d3<d2 d3=d2)
        where
        d3=d2 : d3 == d2
        d3=d2 = antisym-≤ (weaken-< d3<d2) d2≤d3

    trans-≤-< : {d1 d2 d3 : D} -> d1 ≤ d2 -> d2 < d3 -> d1 < d3
    trans-≤-< {d1} {d2} {d3} d1≤d2 d2<d3 =
      unsquash isProp-< (∥-map handle (comparison-< d2 d1 d3 d2<d3))
      where
      handle : (d2 < d1 ⊎ d1 < d3) -> d1 < d3
      handle (inj-r d1<d3) = d1<d3
      handle (inj-l d2<d1) = bot-elim (<->!= d2<d1 d2=d1)
        where
        d2=d1 : d2 == d1
        d2=d1 = antisym-≤ (weaken-< d2<d1) d1≤d2

    convert-≤ : {d1 d2 : D} -> d1 ≤ d2 -> d2 ≮ d1
    convert-≤ d1≤d2 d2<d1 = irrefl-< (trans-≤-< d1≤d2 d2<d1)


module _ {D : Type ℓD} {D# : Rel D ℓ#} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {L : isLinearOrder D<}
         {P : isPartialOrder D≤}
         {A : isTightApartness D#}
         {{LA : ApartLinearOrderStr A L}}
         {{CO : CompatibleOrderStr L P}} where
  private
    instance
      IL = L
      IP = P
      IA = A
      ICO = CO

  strengthen-≤-# : {d1 d2 : D} -> d1 ≤ d2 -> d1 # d2 -> d1 < d2
  strengthen-≤-# {d1} {d2} d1≤d2 d1#d2 = handle (eqInv <>-equiv-# d1#d2)
    where
    handle : (d1 < d2 ⊎ d2 < d1) -> d1 < d2
    handle (inj-l d1<d2) = d1<d2
    handle (inj-r d2<d1) = bot-elim (irrefl-< (trans-≤-< d1≤d2 d2<d1))



module _ {D : Type ℓD} {D< : Rel D ℓ<} (<-Str : isLinearOrder D<) where
  private
    instance
      <-Str-I = <-Str

  record DecidableLinearOrderStr : Type (ℓ-max ℓ< ℓD) where
    no-eta-equality
    pattern
    field
      trichotomous-< : Trichotomous _<_

abstract
  isProp-DecidableLinearOrderStr :
    {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {LO : isLinearOrder D<} ->
    isProp (DecidableLinearOrderStr LO)
  isProp-DecidableLinearOrderStr {LO = LO} dlo1@(record {}) dlo2@(record {}) i = ans
    where
    module _ where
      private
        instance
          ILO : isLinearOrder _
          ILO = LO
      ans : (DecidableLinearOrderStr LO)
      ans = record
        { trichotomous-< =
            isPropΠ2 (\x y -> isProp-Tri<)
              (DecidableLinearOrderStr.trichotomous-< dlo1)
              (DecidableLinearOrderStr.trichotomous-< dlo2)
              i
        }


module _ {D : Type ℓD} {D< : Rel D ℓ<} {<-Str : isLinearOrder D<}
         {{S : DecidableLinearOrderStr <-Str}} where
  open DecidableLinearOrderStr S public

  private
    instance
      <-Str-I = <-Str

  abstract
    stable-< : {d1 d2 : D} -> Stable (d1 < d2)
    stable-< {d1} {d2} ¬¬d1<d2 = handle (trichotomous-< d1 d2)
      where
      handle : Tri< d1 d2 -> d1 < d2
      handle (tri< d1<d2 _ _) = d1<d2
      handle (tri= ¬d1<d2 _ _) = bot-elim (¬¬d1<d2 ¬d1<d2)
      handle (tri> ¬d1<d2 _ _) = bot-elim (¬¬d1<d2 ¬d1<d2)


module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {<-Str : isLinearOrder D<} {≤-Str : isPartialOrder D≤}
         {{S : CompatibleOrderStr <-Str ≤-Str}} {{DS : DecidableLinearOrderStr <-Str}} where
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
      handle (tri= _ d1=d2 _) = inj-r (path-≤ (sym d1=d2))
      handle (tri> _ _ d2<d1) = inj-r (weaken-< d2<d1)

    decide-< : (d1 d2 : D) -> Dec (d1 < d2)
    decide-< d1 d2 = handle (trichotomous-< d1 d2)
      where
      handle : Tri (d1 < d2) (d1 == d2) (d2 < d1) -> Dec (d1 < d2)
      handle (tri< d1<d2 _ _) = yes d1<d2
      handle (tri= d1≮d2 _ _) = no d1≮d2
      handle (tri> d1≮d2 _ _) = no d1≮d2

    decide-≤ : (d1 d2 : D) -> Dec (d1 ≤ d2)
    decide-≤ d1 d2 = handle (trichotomous-< d1 d2)
      where
      handle : Tri (d1 < d2) (d1 == d2) (d2 < d1) -> Dec (d1 ≤ d2)
      handle (tri< d1<d2 _ _) = yes (weaken-< d1<d2)
      handle (tri= _ d1=d2 _) = yes (path-≤ d1=d2)
      handle (tri> _ _ d2<d1) = no (\d1≤d2 -> irrefl-< (trans-<-≤ d2<d1 d1≤d2))

  TotalOrderStr-LinearOrder : TotalOrderStr ≤-Str
  TotalOrderStr-LinearOrder = record
   { connex-≤ = \x y -> ∣ (⊎-map weaken-< (\x -> x)) (split-< x y) ∣
   }

module _ {ℓ≼ ℓD : Level} {D : Type ℓD} (_≼_ : Rel D ℓ≼) where
  record isPreOrder : Type (ℓ-max ℓ≼ ℓD) where
    no-eta-equality
    field
      isProp-≼ : {x y : D} -> isProp (x ≼ y)
      refl-≼ : Reflexive _≼_
      trans-≼ : Transitive _≼_

module _ {ℓ≼ ℓD : Level} {D : Type ℓD} {le : Rel D ℓ≼} {{PO : isPreOrder le}} where
  open isPreOrder PO public

  _≼_ : Rel D ℓ≼
  _≼_ = le

  refl-≼ᵉ : (d : D) -> d ≼ d
  refl-≼ᵉ _ = refl-≼


module _ {ℓ≤ ℓD : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} where
  isPartialOrder->isPreOrder : isPartialOrder D≤ -> isPreOrder D≤
  isPartialOrder->isPreOrder O = record
    { isProp-≼ = isPartialOrder.isProp-≤ O
    ; trans-≼ = isPartialOrder.trans-≤ O
    ; refl-≼ = isPartialOrder.refl-≤ O
    }
