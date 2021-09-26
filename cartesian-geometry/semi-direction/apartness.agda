{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-direction.apartness where

open import additive-group
open import apartness
open import base
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction hiding
  ( _sd#_
  ; sym-sd#
  )
open import cartesian-geometry.semi-rotation
open import cartesian-geometry.vector
open import equality
open import relation
open import set-quotient


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

private
  record _sd#_ (sd1 sd2 : SemiDirection) : Type₁ where
    no-eta-equality
    constructor sd#-cons
    field
      apart : semi-direction-diff sd1 sd2 # zero-semi-rotation

--  sym-sd# : Symmetric _sd#_
--  sym-sd# (sd#-cons d#0) = sd#-cons (subst2 _#_ ? ? ?)
