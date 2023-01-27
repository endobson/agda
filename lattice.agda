{-# OPTIONS --cubical --safe --exact-split #-}

module lattice where

open import base
open import relation
open import order
open import functions

private
  Op₂ : {ℓ : Level} -> Type ℓ -> Type ℓ
  Op₂ D = D -> D -> D

record MeetSemiLatticeStr {ℓD ℓ≤ : Level} {D : Type ℓD} (PO : PartialOrderStr D ℓ≤) :
                          Type (ℓ-max ℓD ℓ≤) where
  private
    module PO = PartialOrderStr PO

  field
    meet : Op₂ D
    meet-≤-left  : {x y : D} -> meet x y PO.≤ x
    meet-≤-right : {x y : D} -> meet x y PO.≤ y
    meet-greatest-≤ : {x y z : D} -> z PO.≤ x -> z PO.≤ y -> z PO.≤ meet x y

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {PO : PartialOrderStr D ℓ≤}
         {{ MS : MeetSemiLatticeStr PO }} where
  open MeetSemiLatticeStr MS public

  private
    instance
      IPO = PO

  meet-≤-path : {x y : D} -> x ≤ y -> meet x y == x
  meet-≤-path x≤y = antisym-≤ meet-≤-left (meet-greatest-≤ refl-≤ x≤y)

  idempotent-meet : Idempotent meet
  idempotent-meet = meet-≤-path refl-≤

  meet-commute : {a b : D} -> meet a b == meet b a
  meet-commute = antisym-≤ (meet-greatest-≤ meet-≤-right meet-≤-left)
                           (meet-greatest-≤ meet-≤-right meet-≤-left)

record JoinSemiLatticeStr {ℓD ℓ≤ : Level} {D : Type ℓD} (PO : PartialOrderStr D ℓ≤) :
                          Type (ℓ-max ℓD ℓ≤) where
  private
    module PO = PartialOrderStr PO

  field
    join : Op₂ D
    join-≤-left  : {x y : D} -> x PO.≤ join x y
    join-≤-right : {x y : D} -> y PO.≤ join x y
    join-least-≤ : {x y z : D} -> x PO.≤ z -> y PO.≤ z -> join x y PO.≤ z

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {PO : PartialOrderStr D ℓ≤}
         {{ JS : JoinSemiLatticeStr PO }} where
  open JoinSemiLatticeStr JS public

  private
    instance
      IPO = PO

  join-≤-path : {x y : D} -> x ≤ y -> join x y == y
  join-≤-path x≤y = antisym-≤ (join-least-≤ x≤y refl-≤) join-≤-right

  idempotent-join : Idempotent join
  idempotent-join = join-≤-path refl-≤

  join-commute : {a b : D} -> join a b == join b a
  join-commute = antisym-≤ (join-least-≤ join-≤-right join-≤-left)
                           (join-least-≤ join-≤-right join-≤-left)
