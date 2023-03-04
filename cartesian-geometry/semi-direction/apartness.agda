{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-direction.apartness where

open import additive-group
open import apartness
open import base
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction
open import cartesian-geometry.semi-rotation
open import cartesian-geometry.vector
open import equality
open import functions
open import funext
open import hlevel
open import relation
open import set-quotient
open import sum
open import truncation
open import vector-space


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

semi-direction-shift : SemiDirection -> SemiRotation -> SemiDirection
semi-direction-shift =
  SemiDirectionElim.rec (isSetΠ (\_ -> isSet-SemiDirection))
    (\d sr -> semi-rotate-direction sr d)
    (\d1 d2 ssd -> funExt (\sr -> a2.srd~ sr d1 d2 ssd))
  where
  f : Rotation -> Direction -> SemiDirection
  f r d = [ rotate-direction r d ]
  module a where
    abstract
      f~ : (r1 r2 : Rotation) -> (SameSemiRotation r1 r2) -> f r1 == f r2
      f~ r1 r2 (same-semi-rotation-same r1=r2) = cong f r1=r2
      f~ r1 r2 (same-semi-rotation-flipped h+r1=r2) =
        funExt (\d -> eq/ (rotate-direction r1 d) (rotate-direction r2 d)
                          (same-semi-direction-flipped (cong fst (p d))))
        where
        p : (d : Direction) -> rotate-direction r1 d == d- (rotate-direction r2 d)
        p d = cong (\r -> rotate-direction r d)
                (sym (add-half-rotation-double-inverse _) >=>
                 cong add-half-rotation h+r1=r2) >=>
              rotate-direction-add-half-rotation r2 d

  semi-rotate-direction : SemiRotation -> Direction -> SemiDirection
  semi-rotate-direction =
    SemiRotationElim.rec (isSetΠ (\_ -> isSet-SemiDirection)) f a.f~

  module a2 where
    abstract
      srd~ : (sr : SemiRotation) -> (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
             semi-rotate-direction sr d1 == semi-rotate-direction sr d2
      srd~ =
        SemiRotationElim.elimProp (\sr -> isPropΠ3 (\_ _ _ -> isSet-SemiDirection _ _)) g
        where
        module _ where
          g : (r : Rotation) (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
              [ rotate-direction r d1 ] == [ rotate-direction r d2 ]
          g r d1 d2 (same-semi-direction-same v1=v2) =
            cong (\d -> [ rotate-direction r d ]) (direction-ext v1=v2)
          g r d1 d2 (same-semi-direction-flipped v1=-v2) =
            eq/ _ _ (same-semi-direction-flipped p)
            where
            v1 = fst d1
            v2 = fst d2
            p : rotate-vector r v1 == v- (rotate-vector r v2)
            p = cong (rotate-vector r) v1=-v2 >=> rotate-v- r v2


private
  semi-direction-shift-zero : (sd : SemiDirection) -> semi-direction-shift sd 0# == sd
  semi-direction-shift-zero =
    SemiDirectionElim.elimProp (\_ -> isSet-SemiDirection _ _)
      (\d -> cong [_] (rotate-direction-zero-rotation d))

  semi-direction-diff-step : (sd1 sd2 : SemiDirection) ->
    semi-direction-shift sd1 (semi-direction-diff sd1 sd2) == sd2
  semi-direction-diff-step =
    SemiDirectionElim.elimProp2 (\_ _ -> isSet-SemiDirection _ _)
      (\d1 d2 -> cong [_] (direction-diff-step d1 d2))


  semi-direction-diff-anticommute : (sd1 sd2 : SemiDirection) ->
    (semi-direction-diff sd1 sd2) == - (semi-direction-diff sd2 sd1)
  semi-direction-diff-anticommute =
    SemiDirectionElim.elimProp2 (\_ _ -> isSet-SemiRotation _ _)
      (\d1 d2 -> cong [_] (direction-diff-anticommute d1 d2))

  semi-direction-diff-self : (sd : SemiDirection) ->
    (semi-direction-diff sd sd) == zero-semi-rotation
  semi-direction-diff-self =
    SemiDirectionElim.elimProp (\_ -> isSet-SemiRotation _ _)
      (\d -> cong [_] (direction-diff-self d))


  semi-direction-diff-trans : (sd1 sd2 sd3 : SemiDirection) ->
    (semi-direction-diff sd1 sd2) + (semi-direction-diff sd2 sd3) ==
    (semi-direction-diff sd1 sd3)
  semi-direction-diff-trans =
    SemiDirectionElim.elimProp3 (\_ _ _ -> isSet-SemiRotation _ _)
      (\d1 d2 d3 -> cong [_] (direction-diff-trans d1 d2 d3))

private
  record _sd#_ (sd1 sd2 : SemiDirection) : Type₁ where
    no-eta-equality ; pattern
    constructor sd#-cons
    field
      apart : semi-direction-diff sd1 sd2 # 0#

  abstract
    isProp-sd# : {sd1 sd2 : SemiDirection} -> isProp (sd1 sd# sd2)
    isProp-sd# {sd1} {sd2} (sd#-cons a1) (sd#-cons a2) = cong sd#-cons (isProp-# a1 a2)

    irrefl-sd# : Irreflexive _sd#_
    irrefl-sd# {sd} (sd#-cons d#0) =
      irrefl-# (subst2 _#_ (semi-direction-diff-self sd) refl d#0)

    sym-sd# : Symmetric _sd#_
    sym-sd# {sd1} {sd2} (sd#-cons d#0) = sd#-cons (subst2 _#_ p minus-zero (minus-preserves-sr# d#0))
      where
      p : - (semi-direction-diff sd1 sd2) == (semi-direction-diff sd2 sd1)
      p = sym (semi-direction-diff-anticommute sd2 sd1)

    comparison-sd# : Comparison _sd#_
    comparison-sd# sd1 sd2 sd3 (sd#-cons d13#0) =
      ∥-map (⊎-map sd#-cons sd#-cons)
        (+-reflects-sr#0 (subst (_# 0#) (sym (semi-direction-diff-trans sd1 sd2 sd3)) d13#0))

    tight-sd# : Tight _sd#_
    tight-sd# {sd1} {sd2} ¬sd1#sd2 =
      sym (sym (semi-direction-diff-step sd1 sd2) >=>
           cong (semi-direction-shift sd1) diff=0 >=>
           semi-direction-shift-zero sd1)

      where
      diff=0 : (semi-direction-diff sd1 sd2) == 0#
      diff=0 = tight-# (¬sd1#sd2 ∘ sd#-cons)

instance
  TightApartnessStr-SemiDirection : TightApartnessStr SemiDirection ℓ-one
  TightApartnessStr-SemiDirection .TightApartnessStr._#_ = _sd#_
  TightApartnessStr-SemiDirection .TightApartnessStr.TightApartness-# =
    tight-sd# , (irrefl-sd# , sym-sd# , comparison-sd#)
  TightApartnessStr-SemiDirection .TightApartnessStr.isProp-# = \x y -> isProp-sd#

module _ {d1 d2 : Direction} where
  private
    v1 = ⟨ d1 ⟩
    v2 = ⟨ d2 ⟩
    sd1 : SemiDirection
    sd1 = [ d1 ]
    sd2 : SemiDirection
    sd2 = [ d2 ]
  split-semi-direction-# : sd1 # sd2 -> (v1 # v2) × (v1 # (v- v2))
  split-semi-direction-# (sd#-cons diff#0) =
    subst2 _#_ (rotate-vector-zero-rotation v1) (cong ⟨_⟩ (direction-diff-step d1 d2))
           (sym-# raw-vs#1) ,
    subst2 _#_
           (sym (rotate-add-half-rotation (add-half-rotation 0#) v1) >=>
            cong (\r -> rotate-vector r v1) (add-half-rotation-double-inverse 0#) >=>
            rotate-vector-zero-rotation v1)
           (cong v-_ (cong ⟨_⟩ (direction-diff-step d1 d2)))
           (v--preserves-# (sym-# raw-vs#2))
    where
    r = direction-diff d1 d2


    rotations-apart = sr#->r# diff#0
    raw-vs#1 : rotate-vector r v1 # rotate-vector 0# v1
    raw-vs#1 = rotate-direction₂-preserves-# (proj₁ rotations-apart) d1
    raw-vs#2 : rotate-vector r v1 # rotate-vector (add-half-rotation 0#) v1
    raw-vs#2 = rotate-direction₂-preserves-# (proj₂ rotations-apart) d1
