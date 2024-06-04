{-# OPTIONS --cubical --safe --exact-split #-}

module rational.heyting-field where

open import additive-group
open import apartness
open import base
open import cubical
open import equality
open import functions
open import funext
open import isomorphism
open import heyting-field
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order
open import relation
open import ring
open import semiring
open import sign
open import sign.instances.rational
open import sum
open import truncation
open import univalence

private
  open Ring Ring-ℚ using (isUnit ; is-unit ; isProp-isUnit)

  f#-path-ℚ : {x y : ℚ} -> (isUnit (diff x y)) == (x # y)
  f#-path-ℚ {x} {y} = isoToPath (isProp->iso forward backward isProp-isUnit isProp-#)
    where
    forward : isUnit (diff x y) -> (x # y)
    forward (is-unit 1/d path) x=y =
      1r!=0r (sym path >=> *-left (+-left (sym x=y) >=> +-inverse) >=> *-left-zero)
    backward : (x # y) -> isUnit (diff x y)
    backward x!=y = is-unit (r1/ d d!=0) (*-commute >=> r1/-inverse d d!=0)
      where
      d = (diff x y)
      d!=0 : d != 0#
      d!=0 d=0 = handle (trichotomous-< x y)
        where
        handle : Tri (x < y) (x == y) (y < x) -> Bot
        handle (tri< x<y _ _) =
          NonZero->¬Zero (subst NonZero d=0 (inj-l (Pos-diffℚ x y x<y))) Zero-0r
        handle (tri= _ x=y _) = (x!=y x=y)
        handle (tri> _ _ y<x) =
          NonZero->¬Zero (subst NonZero (sym diff-anticommute >=> d=0)
                                (inj-r (r--flips-sign _ pos-sign (Pos-diffℚ y x y<x)))) Zero-0r

instance
  RationalField : Field Ring-ℚ isTightApartness-ℚ#
  RationalField = record
    { f#-path = funExt2 (\x y -> f#-path-ℚ)
    }
