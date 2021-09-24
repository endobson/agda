{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-rotation where

open import additive-group
open import base
open import equality
open import hlevel
open import cartesian-geometry.rotation
open import cartesian-geometry.vector
open import cartesian-geometry.semi-direction
open import set-quotient

-- SemiRotation

data SameSemiRotation (r1 r2 : Rotation) : Type₁ where
  same-semi-rotation-same : r1 == r2 -> SameSemiRotation r1 r2
  same-semi-rotation-flipped : add-half-rotation r1 == r2 -> SameSemiRotation r1 r2

SemiRotation : Type₁
SemiRotation = Rotation / SameSemiRotation

isSet-SemiRotation : isSet SemiRotation
isSet-SemiRotation = squash/

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
