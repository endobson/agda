{-# OPTIONS --cubical --safe --exact-split #-}

module order.partial-order where

open import base
open import cubical
open import hlevel
open import relation

import equality-path

private
  variable
    ℓD ℓ≤ : Level

record isPartialOrder {D : Type ℓD} (_≤_ : Rel D ℓ≤)  : Type (ℓ-max ℓ≤ ℓD) where
  no-eta-equality
  pattern
  field
    isProp-≤ : {x y : D} -> isProp (x ≤ y)
    refl-≤ : Reflexive _≤_
    trans-≤ : Transitive _≤_
    antisym-≤ : Antisymmetric _≤_

  _≥_ : D -> D -> Type ℓ≤
  x ≥ y = y ≤ x

  module _ where
    private
      open equality-path
      path-≤ : {x y : D} -> (p : x == y) -> x ≤ y
      path-≤ {x} {y} p = transport (\i -> x ≤ (p i)) refl-≤

      anti-refl : {x : D} -> x == x
      anti-refl = antisym-≤ (path-≤ refl) (path-≤ refl)

      normalize : {x y : D} -> (x == y) -> (x == y)
      normalize p = antisym-≤ (path-≤ p) (path-≤ (sym p))

      normalize-same : {x y : D} -> (p1 p2 : x == y) -> normalize p1 == normalize p2
      normalize-same p1 p2 =
        cong2 antisym-≤ (isProp-≤ _ _) (isProp-≤ _ _)

      normalize-expand : {x y : D} (p : x == y) ->
                         (normalize p >=> refl) == (anti-refl >=> p)
      normalize-expand p i =
        antisym-≤ (path-≤ (\j -> p (~ i ∧ j))) (path-≤ (\j -> p (~ i ∧ ~ j))) >=>
        (\j -> p (~ i ∨ j))

      normalize-inv : {x y : D} -> (x == y) -> (x == y)
      normalize-inv p = (sym anti-refl) >=> p

      normalize-simplify : {x y : D} (p : x == y) -> normalize-inv (normalize p) == p
      normalize-simplify p =
        cong (sym anti-refl >=>_) (sym (compPath-refl-right (normalize p)) >=> (normalize-expand p)) >=>
        sym (compPath-assoc _ _ _) >=>
        cong (_>=> p) (compPath-sym (sym anti-refl)) >=>
        (compPath-refl-left p)

      inhab-isContr : {x y : D} -> (p : x == y) -> isContr (x == y)
      inhab-isContr p =
        normalize-inv (normalize p) ,
        \p2 -> cong normalize-inv (normalize-same p p2) >=> normalize-simplify p2

    abstract
      isSet-D : isSet D
      isSet-D x y p1 = isContr->isProp (inhab-isContr p1) p1


isProp-isPartialOrder : {D : Type ℓD} (_≤_ : Rel D ℓ≤) -> isProp (isPartialOrder _≤_)
isProp-isPartialOrder _ O1@(record {}) O2@(record {}) = \i -> record
  { isProp-≤ = isProp-isProp O1.isProp-≤ O2.isProp-≤ i
  ; refl-≤ = O1.isProp-≤ O1.refl-≤ O2.refl-≤ i
  ; trans-≤ = isPropΠ2 (\_ _ -> O1.isProp-≤) O1.trans-≤ O2.trans-≤ i
  ; antisym-≤ = isPropΠ2 (\_ _ -> O1.isSet-D _ _) O1.antisym-≤ O2.antisym-≤ i
  }
  where
  module O1 = isPartialOrder O1
  module O2 = isPartialOrder O2


record PartialOrderStr (D : Type ℓD) (ℓ≤ : Level) : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
  no-eta-equality
  pattern
  field
    _≤_ : D -> D -> Type ℓ≤
    isPartialOrder-≤ : isPartialOrder _≤_

  open module isPartialOrder-≤ = isPartialOrder isPartialOrder-≤ public
