{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-rotation where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import cartesian-geometry.rotation
open import cartesian-geometry.vector
open import cartesian-geometry.semi-direction
open import set-quotient
open import sigma
open import sum
open import truncation
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

zero-semi-rotation : SemiRotation
zero-semi-rotation = [ zero-rotation ]

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

sr-_ : SemiRotation -> SemiRotation
sr-_ = SemiRotationElim.rec isSet-SemiRotation f a.f~
  where
  f : Rotation -> SemiRotation
  f a = [ - a ]

  module a where
    abstract
      f~ : (r1 r2 : Rotation) -> (SameSemiRotation r1 r2) -> f r1 == f r2
      f~ r1 r2 (same-semi-rotation-same p) = cong f p
      f~ r1 r2 (same-semi-rotation-flipped p) =
        eq/ _ _ (same-semi-rotation-flipped p2)
        where
        p2 = add-half-rotation-minus-commute _ >=>
             cong -_ p

sr-diff : SemiRotation -> SemiRotation -> SemiRotation
sr-diff sr1 sr2 = sr2 sr+ (sr- sr1)

sr-+-inverse : (sr : SemiRotation) -> (sr sr+ (sr- sr)) == zero-semi-rotation
sr-+-inverse =
  SemiRotationElim.elimProp
    (\sr -> isSet-SemiRotation _ _)
    (\r -> cong [_] +-inverse)

sr-+-left-zero : (sr : SemiRotation) -> (zero-semi-rotation sr+ sr) == sr
sr-+-left-zero =
  SemiRotationElim.elimProp
    (\sr -> isSet-SemiRotation _ _)
    (\r -> cong [_] +-left-zero)

sr-+-assoc : (sr1 sr2 sr3 : SemiRotation) -> ((sr1 sr+ sr2) sr+ sr3) == (sr1 sr+ (sr2 sr+ sr3))
sr-+-assoc =
  SemiRotationElim.elimProp3
    (\_ _ _ -> isSet-SemiRotation _ _)
    (\_ _ _ -> cong [_] +-assoc)

sr-+-commute : (sr1 sr2 : SemiRotation) -> (sr1 sr+ sr2) == (sr2 sr+ sr1)
sr-+-commute =
  SemiRotationElim.elimProp2
    (\_ _ -> isSet-SemiRotation _ _)
    (\_ _ -> cong [_] +-commute)


sr-diff-anticommute : (sr1 sr2 : SemiRotation) -> sr-diff sr1 sr2 == sr- (sr-diff sr2 sr1)
sr-diff-anticommute =
  SemiRotationElim.elimProp2
    (\sr1 sr2 -> isSet-SemiRotation _ _)
    (\_ _ -> cong [_] diff-anticommute)


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

¬NonTrivial-zero-semi-rotation : ¬ (NonTrivialSemiRotation zero-semi-rotation)
¬NonTrivial-zero-semi-rotation (non-trivial-semi-rotation 0#0 _) = irrefl-# 0#0

¬NonTrivial->zero-semi-rotation :
  {sr : SemiRotation} -> ¬ (NonTrivialSemiRotation sr) -> (sr == zero-semi-rotation)
¬NonTrivial->zero-semi-rotation {sr} =
  SemiRotationElim.elimProp
    (\sr -> isPropΠ (\(_ : ¬ (NonTrivialSemiRotation sr)) -> isSet-SemiRotation sr _))
    f sr
  where
  f1 : (r : Rotation) -> ¬ (r # 0#) -> [ r ] == zero-semi-rotation
  f1 r ¬r#0 = cong [_] (tight-# ¬r#0)

  f2 : (r : Rotation) -> ¬ (r # half-rotation) -> [ r ] == zero-semi-rotation
  f2 r ¬r#h = cong [_] (tight-# ¬r#h) >=> eq/ _ _ (same-semi-rotation-flipped p)
    where
    p = cong add-half-rotation (sym +-left-zero >=> sym (add-half-rotation-path _)) >=>
        add-half-rotation-double-inverse _

  f : (r : Rotation) -> ¬ (NonTrivialSemiRotation' r) -> [ r ] == zero-semi-rotation
  f r ¬nt = unsquash (isSet-SemiRotation _ _)
              (∥-map handle (comparison-# half-rotation r 0# half-rotation#0))
    where
    handle : (half-rotation # r) ⊎ (r # 0#) -> [ r ] == zero-semi-rotation
    handle (inj-l h#r) =
      f1 r (\ r#0 -> ¬nt (non-trivial-semi-rotation r#0 (sym-# h#r)))
    handle (inj-r r#0) =
      f2 r (\ r#h -> ¬nt (non-trivial-semi-rotation r#0 r#h))



sr--preserves-NonTrivial :
  (sr : SemiRotation) -> NonTrivialSemiRotation sr -> NonTrivialSemiRotation (sr- sr)
sr--preserves-NonTrivial =
  SemiRotationElim.elimProp (\sr -> isPropΠ (\_ -> isProp-NonTrivialSemiRotation (sr- sr))) f
  where
  f : (r : Rotation) -> NonTrivialSemiRotation' r -> NonTrivialSemiRotation' (r- r)
  f r (non-trivial-semi-rotation r#0 r#h) = (non-trivial-semi-rotation -r#0 -r#h)
    where
    -r#0 : (- r) # 0#
    -r#0 = subst ((- r) #_) minus-zero (minus-preserves-r# r#0)
    -r#h : (- r) # half-rotation
    -r#h = subst ((- r) #_) minus-half-rotation (minus-preserves-r# r#h)

record _sr#_ (sr1 sr2 : SemiRotation) : Type₁ where
  no-eta-equality
  constructor sr#-cons
  field
    nt : NonTrivialSemiRotation (sr-diff sr1 sr2)

isProp-sr# : {sr1 sr2 : SemiRotation} -> isProp (sr1 sr# sr2)
isProp-sr# {sr1} {sr2} (sr#-cons nt1) (sr#-cons nt2) =
  cong sr#-cons (isProp-NonTrivialSemiRotation (sr-diff sr1 sr2) nt1 nt2)


sym-sr# : Symmetric _sr#_
sym-sr# {sr1} {sr2} (sr#-cons nt) =
  sr#-cons (subst NonTrivialSemiRotation p (sr--preserves-NonTrivial (sr-diff sr1 sr2) nt))
  where
  p : sr- (sr-diff sr1 sr2) == sr-diff sr2 sr1
  p = sym (sr-diff-anticommute sr2 sr1)

irrefl-sr# : Irreflexive _sr#_
irrefl-sr# {sr} (sr#-cons nt) =
  ¬NonTrivial-zero-semi-rotation (subst NonTrivialSemiRotation (sr-+-inverse sr) nt)

comparison-sr# : (sr1 sr2 sr3 : SemiRotation) -> (sr1 sr# sr3) ->
                 ∥ (sr1 sr# sr2) ⊎ (sr2 sr# sr3) ∥
comparison-sr# =
  SemiRotationElim.elimProp3 (\ _ _ _ -> isPropΠ (\_ -> squash)) f
  where
  f : (r1 r2 r3 : Rotation) -> ([ r1 ] sr# [ r3 ]) -> ∥ ([ r1 ] sr# [ r2 ]) ⊎ ([ r2 ] sr# [ r3 ]) ∥
  f r1 r2 r3 (sr#-cons (non-trivial-semi-rotation 13#0 13#h)) =
    ∥-bind2 handle c1 c2
    where
    Ans = ∥ ([ r1 ] sr# [ r2 ]) ⊎ ([ r2 ] sr# [ r3 ]) ∥
    h = half-rotation

    diffs#00 : ∥ ((diff r1 r2) # 0#) ⊎ ((diff r2 r3) # 0#) ∥
    diffs#00 = +-reflects-r# (subst2 _#_ (sym diff-trans) (sym +-right-zero) 13#0)

    diffs#0h : ∥ ((diff r1 r2) # 0#) ⊎ ((diff r2 r3) # h) ∥
    diffs#0h = +-reflects-r# (subst2 _#_ (sym diff-trans) (sym +-left-zero) 13#h)

    diffs#h0 : ∥ ((diff r1 r2) # h) ⊎ ((diff r2 r3) # 0#) ∥
    diffs#h0 = +-reflects-r# (subst2 _#_ (sym diff-trans) (sym +-right-zero) 13#h)

    diffs#hh : ∥ ((diff r1 r2) # h) ⊎ ((diff r2 r3) # h) ∥
    diffs#hh = +-reflects-r# (subst2 _#_ (sym diff-trans) p 13#0)
      where
      p = sym +-inverse >=> +-right minus-half-rotation


    c1 : ∥ ((diff r1 r2) # h) ⊎ ((diff r1 r2) # 0#) ∥
    c1 = ∥-map (⊎-map-left sym-#) (comparison-# half-rotation (diff r1 r2) 0# half-rotation#0)

    c2 : ∥ ((diff r2 r3) # h) ⊎ ((diff r2 r3) # 0#) ∥
    c2 = ∥-map (⊎-map-left sym-#) (comparison-# half-rotation (diff r2 r3) 0# half-rotation#0)

    handle : (((diff r1 r2) # h) ⊎ ((diff r1 r2) # 0#)) ->
             (((diff r2 r3) # h) ⊎ ((diff r2 r3) # 0#)) ->
             Ans
    handle (inj-l d12#h) (inj-l d23#h) = ∥-bind handle2 diffs#00
      where
      handle2 : ((diff r1 r2) # 0#) ⊎ ((diff r2 r3) # 0#) -> Ans
      handle2 (inj-l d12#0) = ∣ inj-l (sr#-cons (non-trivial-semi-rotation d12#0 d12#h)) ∣
      handle2 (inj-r d23#0) = ∣ inj-r (sr#-cons (non-trivial-semi-rotation d23#0 d23#h)) ∣
    handle (inj-r d12#0) (inj-l d23#h) = ∥-bind handle2 diffs#h0
      where
      handle2 : ((diff r1 r2) # h) ⊎ ((diff r2 r3) # 0#) -> Ans
      handle2 (inj-l d12#h) = ∣ inj-l (sr#-cons (non-trivial-semi-rotation d12#0 d12#h)) ∣
      handle2 (inj-r d23#0) = ∣ inj-r (sr#-cons (non-trivial-semi-rotation d23#0 d23#h)) ∣
    handle (inj-l d12#h) (inj-r d23#0) = ∥-bind handle2 diffs#0h
      where
      handle2 : ((diff r1 r2) # 0#) ⊎ ((diff r2 r3) # h) -> Ans
      handle2 (inj-l d12#0) = ∣ inj-l (sr#-cons (non-trivial-semi-rotation d12#0 d12#h)) ∣
      handle2 (inj-r d23#h) = ∣ inj-r (sr#-cons (non-trivial-semi-rotation d23#0 d23#h)) ∣
    handle (inj-r d12#0) (inj-r d23#0) = ∥-bind handle2 diffs#hh
      where
      handle2 : ((diff r1 r2) # h) ⊎ ((diff r2 r3) # h) -> Ans
      handle2 (inj-l d12#h) = ∣ inj-l (sr#-cons (non-trivial-semi-rotation d12#0 d12#h)) ∣
      handle2 (inj-r d23#h) = ∣ inj-r (sr#-cons (non-trivial-semi-rotation d23#0 d23#h)) ∣


tight-sr# : Tight _sr#_
tight-sr# {sr1} {sr2} ¬sr1#sr2 = sym path
  where
  ¬nt : ¬ (NonTrivialSemiRotation (sr-diff sr1 sr2))
  ¬nt = ¬sr1#sr2 ∘ sr#-cons

  diff-path : (sr-diff sr1 sr2) == zero-semi-rotation
  diff-path = ¬NonTrivial->zero-semi-rotation ¬nt

  path : sr2 == sr1
  path =
    sym (sr-+-left-zero sr2) >=>
    (sr-+-commute zero-semi-rotation sr2) >=>
    cong (sr2 sr+_) (sym (sr-+-inverse sr1) >=> sr-+-commute sr1 (sr- sr1)) >=>
    sym (sr-+-assoc sr2 (sr- sr1) sr1) >=>
    cong (_sr+ sr1) diff-path
    >=> sr-+-left-zero sr1

instance
  TightApartnessStr-SemiRotation : TightApartnessStr SemiRotation
  TightApartnessStr-SemiRotation .TightApartnessStr._#_ = _sr#_
  TightApartnessStr-SemiRotation .TightApartnessStr.TightApartness-# =
    tight-sr# , (irrefl-sr# , sym-sr# , comparison-sr#)
  TightApartnessStr-SemiRotation .TightApartnessStr.isProp-# = \x y -> isProp-sr#



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
