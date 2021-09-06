{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.line where

open import base
open import cartesian-geometry
open import equality
open import functions
open import hlevel
open import isomorphism
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.order
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import set-quotient
open import sigma
open import truncation
open import univalence
open import vector-space

record LineSegment (p1 p2 : Point) : Type₁ where
  field
    distinct : p1 P# p2

record RayFrom (p : Point) : Type₁ where
  field
    direction : Direction

Ray : Type₁
Ray = Σ Point RayFrom


Line' : Type₁
Line' = Point × SemiDirection

-- OnLine' : REL Line' Point ℓ-one
-- OnLine' (o , s) p = vector->semi-direction (P-diff o p)
