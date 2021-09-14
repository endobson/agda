{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.line where

open import base
open import cartesian-geometry
open import cartesian-geometry.vector
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
open import subset
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

line'-point : Line' -> Point
line'-point (p , _) = p

line'-semi-direction : Line' -> SemiDirection
line'-semi-direction (_ , s) = s

OnLine' : Line' -> Subtype Point ℓ-one
OnLine' (o , s) p = semi-direction-span s (P-diff o p)

-- OnLine'-self : (l : Line') -> ⟨ OnLine' l (line'-point l) ⟩
-- OnLine'-self (p , s) = subst (\v -> ⟨ semi-direction-span s v ⟩) (sym dpp) semi-direction-span-0v
--   where
--   semi-direction-span-0v : ⟨ semi-direction-span s 0v ⟩
--   semi-direction-span-0v = ?
--
--   dpp : P-diff p p == 0v
--   dpp = ?

SameLine' : Rel Line' ℓ-one
SameLine' l1@(p1 , s1) l2@(p2 , s2) = ⟨ OnLine' l1 p2 ⟩ × ⟨ OnLine' l2 p1 ⟩ × s1 == s2

Line : Type ℓ-one
Line = Line' / SameLine'

line-slope : Line -> SemiDirection
line-slope =
  SetQuotientElim.rec Line' SameLine' isSet-SemiDirection
    line'-semi-direction
    (\_ _ (_ , _ , p) -> p)
