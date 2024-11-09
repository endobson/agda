{-# OPTIONS --cubical --safe --exact-split #-}

module lattice where

open import base
open import relation
open import order
open import hlevel.base
open import functions
open import funext

private
  Op₂ : {ℓ : Level} -> Type ℓ -> Type ℓ
  Op₂ D = D -> D -> D

record isMeetOp {ℓD ℓ≤ : Level} {D : Type ℓD} {_≤_ : Rel D ℓ≤}
                (PO : isPartialOrder _≤_) (meet : Op₂ D) : Type (ℓ-max ℓD ℓ≤) where
  field
    meet-≤-left  : {x y : D} -> meet x y ≤ x
    meet-≤-right : {x y : D} -> meet x y ≤ y
    meet-greatest-≤ : {x y z : D} -> z ≤ x -> z ≤ y -> z ≤ meet x y


record isJoinOp {ℓD ℓ≤ : Level} {D : Type ℓD} {_≤_ : Rel D ℓ≤}
                (PO : isPartialOrder _≤_) (join : Op₂ D) : Type (ℓ-max ℓD ℓ≤) where
  field
    join-≤-left  : {x y : D} -> x ≤ join x y
    join-≤-right : {x y : D} -> y ≤ join x y
    join-least-≤ : {x y z : D} -> x ≤ z -> y ≤ z -> join x y ≤ z

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} (PO : isPartialOrder D≤) (op : Op₂ D) where
  private
    instance
      IPO = PO

  isProp-isMeetOp : isProp (isMeetOp PO op)
  isProp-isMeetOp im1 im2 i = record
    { meet-≤-left  = isProp-≤ im1.meet-≤-left im2.meet-≤-left i
    ; meet-≤-right = isProp-≤ im1.meet-≤-right im2.meet-≤-right i
    ; meet-greatest-≤ = isPropΠ2 (\_ _ -> isProp-≤) im1.meet-greatest-≤ im2.meet-greatest-≤ i
    }
    where
    module im1 = isMeetOp im1
    module im2 = isMeetOp im2

  isProp-isJoinOp : isProp (isJoinOp PO op)
  isProp-isJoinOp ij1 ij2 i = record
    { join-≤-left  = isProp-≤ ij1.join-≤-left ij2.join-≤-left i
    ; join-≤-right = isProp-≤ ij1.join-≤-right ij2.join-≤-right i
    ; join-least-≤ = isPropΠ2 (\_ _ -> isProp-≤) ij1.join-least-≤ ij2.join-least-≤ i
    }
    where
    module ij1 = isJoinOp ij1
    module ij2 = isJoinOp ij2


record MeetSemiLatticeStr {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} (PO : isPartialOrder D≤) :
                          Type (ℓ-max ℓD ℓ≤) where
  field
    meet : Op₂ D
    is-meet-op : isMeetOp PO meet

  open module is-meet-op = isMeetOp is-meet-op public

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤} where
  private
    instance
      IPO = PO

  isProp-MeetSemiLatticeStr : isProp (MeetSemiLatticeStr PO)
  isProp-MeetSemiLatticeStr m1 m2 i = record
    { meet = path i
    ; is-meet-op = isProp->PathPᵉ (\i -> isProp-isMeetOp PO (path i)) m1.is-meet-op m2.is-meet-op i
    }
    where
    module m1 = MeetSemiLatticeStr m1
    module m2 = MeetSemiLatticeStr m2

    path' : (x y : D) -> m1.meet x y == m2.meet x y
    path' x y = antisym-≤ (m2.meet-greatest-≤ m1.meet-≤-left m1.meet-≤-right)
                          (m1.meet-greatest-≤ m2.meet-≤-left m2.meet-≤-right)

    path : m1.meet == m2.meet
    path = funExt (\x -> (funExt (\y -> path' x y)))


module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤}
         {{ MS : MeetSemiLatticeStr PO }} where
  open MeetSemiLatticeStr MS public hiding
    ( is-meet-op
    )

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

record JoinSemiLatticeStr {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} (PO : isPartialOrder D≤) :
                          Type (ℓ-max ℓD ℓ≤) where
  field
    join : Op₂ D
    is-join-op : isJoinOp PO join

  open module is-join-op = isJoinOp is-join-op public

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤} where
  private
    instance
      IPO = PO

  isProp-JoinSemiLatticeStr : isProp (JoinSemiLatticeStr PO)
  isProp-JoinSemiLatticeStr j1 j2 i = record
    { join = path i
    ; is-join-op = isProp->PathPᵉ (\i -> isProp-isJoinOp PO (path i)) j1.is-join-op j2.is-join-op i
    }
    where
    module j1 = JoinSemiLatticeStr j1
    module j2 = JoinSemiLatticeStr j2

    path' : (x y : D) -> j1.join x y == j2.join x y
    path' x y = antisym-≤ (j1.join-least-≤ j2.join-≤-left j2.join-≤-right)
                          (j2.join-least-≤ j1.join-≤-left j1.join-≤-right)


    path : j1.join == j2.join
    path = funExt (\x -> (funExt (\y -> path' x y)))


module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤}
         {{ JS : JoinSemiLatticeStr PO }} where
  open JoinSemiLatticeStr JS public hiding
    ( is-join
    )

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
