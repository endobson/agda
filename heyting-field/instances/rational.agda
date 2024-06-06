{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field.instances.rational where

open import additive-group
open import apartness
open import base
open import equality
open import funext
open import isomorphism
open import heyting-field
open import order
open import ordered-additive-group
open import rational
open import rational.order
open import relation
open import ring
open import semiring
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
        handle : Tri< x y -> Bot
        handle (tri< x<y _ _) = irrefl-< (trans-<-= (diff-0<⁺ x<y) d=0)
        handle (tri= _ x=y _) = (x!=y x=y)
        handle (tri> _ _ y<x) = irrefl-< (trans-<-= (diff-<0⁺ y<x) (sym d=0))

instance
  Field-ℚ : Field Ring-ℚ isTightApartness-ℚ#
  Field-ℚ = record
    { f#-path = funExt2 (\x y -> f#-path-ℚ)
    }
