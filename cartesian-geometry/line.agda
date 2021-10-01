{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.line where

open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry
open import cartesian-geometry.vector
open import cartesian-geometry.semi-direction
open import cartesian-geometry.semi-direction.apartness
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
  no-eta-equality
  constructor line-segment-cons
  field
    distinct : p1 P# p2

record RayFrom (p : Point) : Type₁ where
  no-eta-equality
  constructor ray-cons
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

line-semi-direction : Line -> SemiDirection
line-semi-direction =
  SetQuotientElim.rec Line' SameLine' isSet-SemiDirection
    line'-semi-direction
    (\_ _ (_ , _ , p) -> p)

ParallelLines : Rel Line ℓ-one
ParallelLines l1 l2 = (line-semi-direction l1) == (line-semi-direction l2)

ConvergentLines : Rel Line ℓ-one
ConvergentLines l1 l2 = (line-semi-direction l1) # (line-semi-direction l2)

OnLine'-SameLine' : (l1 l2 : Line') -> SameLine' l1 l2 -> OnLine' l1 == OnLine' l2
OnLine'-SameLine' l1 l2 (p2∈l1 , p1∈l2 , s1=s2) =
  same-Subtype (f p1∈l2 s1=s2) (f p2∈l1 (sym s1=s2))
  where
  f : {l1 l2 : Line'} -> ⟨ OnLine' l2 (line'-point l1) ⟩ ->
      line'-semi-direction l1 == line'-semi-direction l2 ->
      {d : Point} -> ⟨ OnLine' l1 d ⟩ -> ⟨ OnLine' l2 d ⟩
  f {p1 , s1} {p2 , s2} p1∈l2 s1=s2 {d} d∈l1 =
    subst (\v -> ⟨ semi-direction-span s2 v ⟩) (P-diff-trans p2 p1 d) check3
    where
    check1 : ⟨ semi-direction-span s2 (P-diff p2 p1) ⟩
    check1 = p1∈l2

    check2 : ⟨ semi-direction-span s2 (P-diff p1 d) ⟩
    check2 = subst (\s -> ⟨ semi-direction-span s (P-diff p1 d) ⟩) s1=s2 d∈l1

    check3 : ⟨ semi-direction-span s2 (P-diff p2 p1 v+ P-diff p1 d) ⟩
    check3 = isLinearSubtype.closed-under-v+ (isLinearSubtype-semi-direction-span s2) check1 check2

OnLine : Line -> Subtype Point ℓ-one
OnLine =
  SetQuotientElim.rec Line' SameLine' isSet-Subtype OnLine' OnLine'-SameLine'


-- Standard lines

direction-line' : Direction -> Line'
direction-line' d = 0P , [ d ]

semi-direction-line' : SemiDirection -> Line'
semi-direction-line' sd = 0P , sd

xaxis-line' : Line'
xaxis-line' = direction-line' xaxis-dir
xaxis-line : Line
xaxis-line = [ xaxis-line' ]

yaxis-line' : Line'
yaxis-line' = direction-line' yaxis-dir
yaxis-line : Line
yaxis-line = [ yaxis-line' ]

line-segment->line : {p1 p2 : Point} -> LineSegment p1 p2 -> Line
line-segment->line {p1} {p2} l =
  [ p1 , (vector->semi-direction (P-diff p1 p2) (P#->P-diff#0 p1 p2 (LineSegment.distinct l))) ]
