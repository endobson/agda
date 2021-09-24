{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-rotation where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import hlevel
open import isomorphism
open import cartesian-geometry.rotation
open import cartesian-geometry.vector
open import cartesian-geometry.semi-direction
open import set-quotient
open import sigma
open import relation
open import univalence

-- SemiRotation

data SameSemiRotation (r1 r2 : Rotation) : Type₁ where
  same-semi-rotation-same : r1 == r2 -> SameSemiRotation r1 r2
  same-semi-rotation-flipped : add-half-rotation r1 == r2 -> SameSemiRotation r1 r2

SemiRotation : Type₁
SemiRotation = Rotation / SameSemiRotation

module SemiRotationElim = SetQuotientElim Rotation SameSemiRotation

isSet-SemiRotation : isSet SemiRotation
isSet-SemiRotation = squash/


_sr+_ : SemiRotation -> SemiRotation -> SemiRotation
_sr+_ = SemiRotationElim.rec2 isSet-SemiRotation f a.f~₁ a.f~₂
  where
  f : Rotation -> Rotation -> SemiRotation
  f a b = [ a + b ]

  module a where
    abstract
      f~₁ : (r1 r2 r3 : Rotation) -> (SameSemiRotation r1 r2) -> f r1 r3 == f r2 r3
      f~₁ r1 r2 r3 (same-semi-rotation-same p) = cong (\r -> f r r3) p
      f~₁ r1 r2 r3 (same-semi-rotation-flipped p) =
        eq/ _ _ (same-semi-rotation-flipped p2)
        where
        p2 = add-half-rotation-path _ >=>
             +-left +-commute >=> +-assoc >=> +-commute >=>
             +-left (sym (add-half-rotation-path _) >=> p)

      f~₂ : (r1 r2 r3 : Rotation) -> (SameSemiRotation r2 r3) -> f r1 r2 == f r1 r3
      f~₂ r1 r2 r3 sr = cong [_] +-commute >=> f~₁ r2 r3 r1 sr >=> cong [_] +-commute



record NonTrivialSemiRotation' (r : Rotation) : Type₁ where
  no-eta-equality
  constructor non-trivial-semi-rotation
  field
    apart-zero : r # zero-rotation
    apart-half : r # half-rotation

isProp-NonTrivialSemiRotation' : {r : Rotation} -> isProp (NonTrivialSemiRotation' r)
isProp-NonTrivialSemiRotation' nt1@(non-trivial-semi-rotation az1 ah1)
                               nt2@(non-trivial-semi-rotation az2 ah2) = a.path
  where
  module a where
    abstract
      path : nt1 == nt2
      path i = non-trivial-semi-rotation (isProp-# az1 az2 i) (isProp-# ah1 ah2 i)

private
  NonTrivialSemiRotation-full : (sr : SemiRotation) -> hProp ℓ-one
  NonTrivialSemiRotation-full =
    SemiRotationElim.rec isSet-hProp f a.preserved
    where
    f : Rotation -> hProp ℓ-one
    f r = NonTrivialSemiRotation' r , isProp-NonTrivialSemiRotation'

    path-preserves : {r1 r2 : Rotation} -> add-half-rotation r1 == r2 ->
                     NonTrivialSemiRotation' r1 -> NonTrivialSemiRotation' r2
    path-preserves {r1} {r2} path (non-trivial-semi-rotation r1#0 r1#h) =
      (non-trivial-semi-rotation r2#0 r2#h)
      where
      hh=z : half-rotation + half-rotation == zero-rotation
      hh=z =
        sym +-left-zero >=>
        sym +-assoc >=>
        sym (add-half-rotation-path _) >=>
        cong add-half-rotation (sym (add-half-rotation-path _)) >=>
        add-half-rotation-double-inverse _



      r2#0 : r2 # zero-rotation
      r2#0 = subst2 _#_ (sym (add-half-rotation-path _) >=> path) hh=z
                    (+₂-preserves-r# r1#h)
      r2#h : r2 # half-rotation
      r2#h = subst2 _#_ (sym (add-half-rotation-path _) >=> path) +-left-zero
                    (+₂-preserves-r# r1#0)


    module a where
      abstract
        preserved : (r1 r2 : Rotation) (sr : SameSemiRotation r1 r2) -> f r1 == f r2
        preserved r1 r2 (same-semi-rotation-same p) = cong f p
        preserved r1 r2 (same-semi-rotation-flipped p) =
          ΣProp-path isProp-isProp
            (ua (isoToEquiv (isProp->iso (path-preserves p) (path-preserves p2)
                                         isProp-NonTrivialSemiRotation'
                                         isProp-NonTrivialSemiRotation')))
          where
          p2 = cong add-half-rotation (sym p) >=> add-half-rotation-double-inverse _


  NonTrivialSemiRotation : Pred SemiRotation ℓ-one
  NonTrivialSemiRotation s = fst (NonTrivialSemiRotation-full s)

  isProp-NonTrivialSemiRotation : (sr : SemiRotation) -> isProp (NonTrivialSemiRotation sr)
  isProp-NonTrivialSemiRotation sr = snd (NonTrivialSemiRotation-full sr)




semi-direction-diff : (sd1 sd2 : SemiDirection) -> SemiRotation
semi-direction-diff =
  SemiDirectionElim.rec2 isSet-SemiRotation f a.f~₁ a.f~₂
  where
  f : Direction -> Direction -> SemiRotation
  f d1 d2 = [ direction-diff d1 d2 ]

  module a where
    abstract
      f~₁ : (d1 d2 d3 : Direction) -> (SameSemiDirection d1 d2) -> f d1 d3 == f d2 d3
      f~₁ d1 d2 d3 (same-semi-direction-same v1=v2) = cong (\d -> f d d3) (direction-ext v1=v2)
      f~₁ d1 d2 d3 (same-semi-direction-flipped v1=-v2) =
        eq/ (direction-diff d1 d3) (direction-diff d2 d3) (same-semi-rotation-flipped r-path)
        where
        d1=-d2 : d1 == (d- d2)
        d1=-d2 = direction-ext v1=-v2

        r-path : add-half-rotation (direction-diff d1 d3) == direction-diff d2 d3
        r-path =
          add-half-rotation-path _ >=>
          +-assoc >=>
          +-right (sym (add-half-rotation-path _) >=>
                   add-half-rotation-minus-commute _ >=>
                   cong -_ (add-half-rotation-direction->rotation _ >=>
                            cong direction->rotation (cong d-_ d1=-d2 >=> d--double-inverse _)))

      f~₂ : (d1 d2 d3 : Direction) -> (SameSemiDirection d2 d3) -> f d1 d2 == f d1 d3
      f~₂ d1 d2 d3 (same-semi-direction-same d2=d3) = cong (\d -> f d1 d) (direction-ext d2=d3)
      f~₂ d1 d2 d3 (same-semi-direction-flipped v2=-v3) =
        eq/ (direction-diff d1 d2) (direction-diff d1 d3) (same-semi-rotation-flipped r-path)
        where
        d2=-d3 : d2 == (d- d3)
        d2=-d3 = direction-ext v2=-v3

        r-path : add-half-rotation (direction-diff d1 d2) == direction-diff d1 d3
        r-path =
          add-half-rotation-path _ >=>
          +-left +-commute >=> +-assoc >=> +-commute >=>
          +-left (sym (add-half-rotation-path _) >=>
                  add-half-rotation-direction->rotation _ >=>
                  cong direction->rotation (cong d-_ d2=-d3 >=> d--double-inverse _))
