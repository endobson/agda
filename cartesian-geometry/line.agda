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
open import hlevel
open import real
open import relation
open import set-quotient
open import subset
open import truncation
open import vector-space

record LineSegment (p1 p2 : Point) : Type₁ where
  no-eta-equality
  constructor line-segment-cons
  field
    distinct : p1 # p2

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

OnLine'-self : (l : Line') -> ⟨ OnLine' l (line'-point l) ⟩
OnLine'-self (p , s) =
  subst (\v -> ⟨ semi-direction-span s v ⟩) (sym dpp) semi-direction-span-0v
  where
  semi-direction-span-0v : ⟨ semi-direction-span s 0v ⟩
  semi-direction-span-0v =
    isLinearSubtype.closed-under-0v (isLinearSubtype-semi-direction-span s)

  dpp : P-diff p p == 0v
  dpp = cong (P-diff p) (sym (P-shift-0v p)) >=>
        P-shift-step p 0v

SameLine' : Rel Line' ℓ-one
SameLine' l1@(p1 , s1) l2@(p2 , s2) = ⟨ OnLine' l1 p2 ⟩ × ⟨ OnLine' l2 p1 ⟩ × s1 == s2

module _ {l1 l2 : Line'} where
  private
    p1 = line'-point l1
    p2 = line'-point l2
    sd1 = line'-semi-direction l1
    sd2 = line'-semi-direction l2
  simple-SameLine' : ⟨ OnLine' l1 p2 ⟩ -> sd1 == sd2 -> SameLine' l1 l2
  simple-SameLine' ol sd1=sd2 = ol , ol2 , sd1=sd2
    where
    ol2 : ⟨ OnLine' l2 p1 ⟩
    ol2 = subst (\v -> ⟨ semi-direction-span sd2 v ⟩) (sym (P-diff-anticommute p2 p1))
            (isLinearSubtype.closed-under-v- (isLinearSubtype-semi-direction-span sd2)
               (subst (\sd -> ⟨ semi-direction-span sd (P-diff p1 p2) ⟩) sd1=sd2 ol))

Line : Type ℓ-one
Line = Line' / SameLine'

isSet-Line : isSet Line
isSet-Line = squash/

line-semi-direction : Line -> SemiDirection
line-semi-direction =
  SetQuotientElim.rec isSet-SemiDirection
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
OnLine = SetQuotientElim.rec isSet-Subtype OnLine' OnLine'-SameLine'


abstract
  OnLine-path : {p : Point} {l : Line} -> ⟨ OnLine l p ⟩ -> l == [ p , (line-semi-direction l) ]
  OnLine-path {p} {l} =
    SetQuotientElim.elimProp
      (\l -> (isPropΠ (\(_ : ⟨ OnLine l p ⟩) -> isSet-Line l [ p , (line-semi-direction l)])))
      (\l' ol' -> eq/ _ _ (simple-SameLine' ol' refl))
      l



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


line-segment->line' : {p1 p2 : Point} -> LineSegment p1 p2 -> Line'
line-segment->line' {p1} {p2} l =
  p1 , (vector->semi-direction (P-diff p1 p2) (p#->P-diff#0 p1 p2 (LineSegment.distinct l)))

line-segment->line : {p1 p2 : Point} -> LineSegment p1 p2 -> Line
line-segment->line {p1} {p2} l = [ line-segment->line' l ]

OnLine-line-segment-start :
  {p1 p2 : Point} -> (l : LineSegment p1 p2) -> ⟨ OnLine (line-segment->line l) p1 ⟩
OnLine-line-segment-start l =  OnLine'-self (line-segment->line' l)

OnLine-line-segment-end :
  {p1 p2 : Point} -> (l : LineSegment p1 p2) -> ⟨ OnLine (line-segment->line l) p2 ⟩
OnLine-line-segment-end {p1} {p2} l =
  vector-length (P-diff p1 p2) ,
  sym (normalize-vector-path (P-diff p1 p2)
                             (p#->P-diff#0 p1 p2 (LineSegment.distinct l)))

flip-line-segment : {a b : Point} -> LineSegment a b -> LineSegment b a
flip-line-segment l = line-segment-cons (sym-# (LineSegment.distinct l))

flip-line-segment-path :
  {a b : Point} -> (l : LineSegment a b) ->
  (line-segment->line (flip-line-segment l)) == (line-segment->line l)
flip-line-segment-path {p1} {p2} ls = eq/ _ _ sl
  where
  fls = (flip-line-segment ls)
  l'1 = (line-segment->line' fls)
  l'2 = (line-segment->line' ls)

  d1 = (vector->direction (P-diff p1 p2) (p#->P-diff#0 p1 p2 (LineSegment.distinct ls)))
  d2 = (vector->direction (P-diff p2 p1) (p#->P-diff#0 p2 p1 (LineSegment.distinct fls)))

  same-sd : SameSemiDirection d2 d1
  same-sd =
    same-semi-direction-flipped
      (sym (normalize-vector-v-'
             (P-diff p1 p2) (p#->P-diff#0 p1 p2 (LineSegment.distinct ls))
             (P-diff p2 p1) (p#->P-diff#0 p2 p1 (LineSegment.distinct fls))
             (P-diff-anticommute p1 p2)))

  sl : SameLine' l'1 l'2
  sl = (OnLine-line-segment-end fls) , (OnLine-line-segment-end ls) , (eq/ _ _ same-sd)

line->line-segment : (l : Line) ->
  ∃[ p1 ∈ Point ] Σ[ p2 ∈ Point ] Σ[ ls ∈ LineSegment p1 p2 ] (line-segment->line ls == l)
line->line-segment = SetQuotientElim.elimProp isProp-Ans f
  where
  Ans : Line -> Type ℓ-one
  Ans l = ∃[ p1 ∈ Point ] Σ[ p2 ∈ Point ] Σ[ ls ∈ LineSegment p1 p2 ] (line-segment->line ls == l)
  isProp-Ans : (l : Line) -> isProp (Ans l)
  isProp-Ans _ = squash
  f : (l : Line') -> Ans [ l ]
  f l@(p1 , sd) = SetQuotientElim.elimProp (\sd -> isProp-Ans [ (p1 , sd) ]) g sd
    where
    g : (d : Direction) -> Ans [ (p1 , [ d ]) ]
    g d@(v , _) = ∣ p1 , p2 , line-segment-cons p1#p2 , line-path ∣
      where
      p2 = P-shift p1 v
      v#0 : v # 0v
      v#0 = direction-#0 d
      p1p2#0 : P-diff p1 p2 # 0v
      p1p2#0 = subst (_# 0v) (sym (P-shift-step p1 v)) v#0
      p1#p2 : p1 # p2
      p1#p2 = P-diff#0->p# _ _ p1p2#0

      dov-1 : DirectionOfVector' (P-diff p1 p2)
                                 (vector->direction (P-diff p1 p2) (p#->P-diff#0 p1 p2 p1#p2))
      dov-1 = DirectionOfVector'-vector->direction (p#->P-diff#0 p1 p2 p1#p2)

      dov-2 : DirectionOfVector' (P-diff p1 p2) d
      dov-2 = subst (\v -> (DirectionOfVector' v d)) (sym (P-shift-step p1 v))
                    DirectionOfVector'-direction

      d-path : (vector->direction (P-diff p1 p2) (p#->P-diff#0 p1 p2 p1#p2)) == d
      d-path = cong fst (isProp-DirectionOfVector (_ , dov-1) (_ , dov-2))

      line-path : line-segment->line (line-segment-cons p1#p2) == [ p1 , [ d ] ]
      line-path i = [ p1 , [ d-path i ] ]
