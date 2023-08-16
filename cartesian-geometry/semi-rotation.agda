{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-rotation where

open import additive-group
open import apartness
open import base
open import equality
open import functions
open import monoid
open import commutative-monoid
open import hlevel
open import isomorphism
open import cartesian-geometry.rotation
open import set-quotient
open import sigma.base
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

module _ where
  zero-semi-rotation : SemiRotation
  zero-semi-rotation = [ zero-rotation ]

  private
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
            p2 : add-half-rotation (r1 + r3) == (r2 + r3)
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
            p2 : add-half-rotation (- r1) == (- r2)
            p2 = add-half-rotation-minus-commute _ >=>
                 cong -_ p

    sr+-inverse : (sr : SemiRotation) -> (sr sr+ (sr- sr)) == zero-semi-rotation
    sr+-inverse =
      SemiRotationElim.elimProp
        (\sr -> isSet-SemiRotation _ _)
        (\r -> cong [_] +-inverse)

    sr+-left-zero : (sr : SemiRotation) -> (zero-semi-rotation sr+ sr) == sr
    sr+-left-zero =
      SemiRotationElim.elimProp
        (\sr -> isSet-SemiRotation _ _)
        (\r -> cong [_] +-left-zero)

    sr+-right-zero : (sr : SemiRotation) -> (sr sr+ zero-semi-rotation) == sr
    sr+-right-zero =
      SemiRotationElim.elimProp
        (\sr -> isSet-SemiRotation _ _)
        (\r -> cong [_] +-right-zero)

    sr+-assoc : (sr1 sr2 sr3 : SemiRotation) -> ((sr1 sr+ sr2) sr+ sr3) == (sr1 sr+ (sr2 sr+ sr3))
    sr+-assoc =
      SemiRotationElim.elimProp3
        (\_ _ _ -> isSet-SemiRotation _ _)
        (\_ _ _ -> cong [_] +-assoc)

    sr+-commute : (sr1 sr2 : SemiRotation) -> (sr1 sr+ sr2) == (sr2 sr+ sr1)
    sr+-commute =
      SemiRotationElim.elimProp2
        (\_ _ -> isSet-SemiRotation _ _)
        (\_ _ -> cong [_] +-commute)


    Monoid-SemiRotation : Monoid SemiRotation
    Monoid-SemiRotation = record
      { ε = zero-semi-rotation
      ; _∙_ = _sr+_
      ; ∙-assoc = \{sr1} {sr2} {sr3} -> sr+-assoc sr1 sr2 sr3
      ; ∙-left-ε = \{sr} -> sr+-left-zero sr
      ; ∙-right-ε = \{sr} -> sr+-right-zero sr
      ; isSet-Domain = isSet-SemiRotation
      }

    CommMonoid-SemiRotation : CommMonoid SemiRotation
    CommMonoid-SemiRotation = record
      { monoid = Monoid-SemiRotation
      ; ∙-commute = \{r1} {r2} -> sr+-commute r1 r2
      }

  instance
    AdditiveCommMonoid-SemiRotation : AdditiveCommMonoid SemiRotation
    AdditiveCommMonoid-SemiRotation = record { comm-monoid = CommMonoid-SemiRotation }

    AdditiveGroup-SemiRotation : AdditiveGroup AdditiveCommMonoid-SemiRotation
    AdditiveGroup-SemiRotation = record { -_ = sr-_ ; +-inverse = \{sr} -> sr+-inverse sr }

private

  record NonTrivialSemiRotation' (r : Rotation) : Type₁ where
    no-eta-equality ; pattern
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
          p2 : add-half-rotation r2 == r1
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


  sr+-reflects-NonTrivial : (sr1 sr2 : SemiRotation) ->
    NonTrivialSemiRotation (sr1 + sr2) ->
    ∥ NonTrivialSemiRotation sr1 ⊎ NonTrivialSemiRotation sr2 ∥
  sr+-reflects-NonTrivial =
    SemiRotationElim.elimProp2 (\sr1 sr2 -> isPropΠ (\_ -> squash)) f
    where
    f : (r1 r2 : Rotation) -> NonTrivialSemiRotation' (r1 + r2) ->
       ∥ NonTrivialSemiRotation' r1 ⊎ NonTrivialSemiRotation' r2 ∥
    f r1 r2 (non-trivial-semi-rotation 12#0 12#h) =
      ∥-bind2 handle c1 c2
      where
      Ans = ∥ (NonTrivialSemiRotation' r1) ⊎ (NonTrivialSemiRotation' r2) ∥
      h = half-rotation

      r12#00 : ∥ (r1 # 0#) ⊎ (r2 # 0#) ∥
      r12#00 = +-reflects-r# (subst2 _#_ refl (sym +-right-zero) 12#0)

      r12#0h : ∥ (r1 # 0#) ⊎ (r2 # h) ∥
      r12#0h = +-reflects-r# (subst2 _#_ refl (sym +-left-zero) 12#h)

      r12#h0 : ∥ (r1 # h) ⊎ (r2 # 0#) ∥
      r12#h0 = +-reflects-r# (subst2 _#_ refl (sym +-right-zero) 12#h)

      r12#hh : ∥ (r1 # h) ⊎ (r2 # h) ∥
      r12#hh = +-reflects-r# (subst2 _#_ refl p 12#0)
        where
        p = sym +-inverse >=> +-right minus-half-rotation

      c1 : ∥ (r1 # h) ⊎ (r1 # 0#) ∥
      c1 = ∥-map (⊎-map-left sym-#) (comparison-# half-rotation r1 0# half-rotation#0)

      c2 : ∥ (r2 # h) ⊎ (r2 # 0#) ∥
      c2 = ∥-map (⊎-map-left sym-#) (comparison-# half-rotation r2 0# half-rotation#0)

      handle : ((r1 # h) ⊎ (r1 # 0#)) -> ((r2 # h) ⊎ (r2 # 0#)) ->
               Ans
      handle (inj-l r1#h) (inj-l r2#h) = ∥-bind handle2 r12#00
        where
        handle2 : (r1 # 0#) ⊎ (r2 # 0#) -> Ans
        handle2 (inj-l r1#0) = ∣ inj-l (non-trivial-semi-rotation r1#0 r1#h) ∣
        handle2 (inj-r r2#0) = ∣ inj-r (non-trivial-semi-rotation r2#0 r2#h) ∣
      handle (inj-r r1#0) (inj-l r2#h) = ∥-bind handle2 r12#h0
        where
        handle2 : (r1 # h) ⊎ (r2 # 0#) -> Ans
        handle2 (inj-l r1#h) = ∣ inj-l (non-trivial-semi-rotation r1#0 r1#h) ∣
        handle2 (inj-r r2#0) = ∣ inj-r (non-trivial-semi-rotation r2#0 r2#h) ∣
      handle (inj-l r1#h) (inj-r r2#0) = ∥-bind handle2 r12#0h
        where
        handle2 : (r1 # 0#) ⊎ (r2 # h) -> Ans
        handle2 (inj-l r1#0) = ∣ inj-l (non-trivial-semi-rotation r1#0 r1#h) ∣
        handle2 (inj-r r2#h) = ∣ inj-r (non-trivial-semi-rotation r2#0 r2#h) ∣
      handle (inj-r r1#0) (inj-r r2#0) = ∥-bind handle2 r12#hh
        where
        handle2 : (r1 # h) ⊎ (r2 # h) -> Ans
        handle2 (inj-l r1#h) = ∣ inj-l (non-trivial-semi-rotation r1#0 r1#h) ∣
        handle2 (inj-r r2#h) = ∣ inj-r (non-trivial-semi-rotation r2#0 r2#h) ∣




  sr--preserves-NonTrivial :
    (sr : SemiRotation) -> NonTrivialSemiRotation sr -> NonTrivialSemiRotation (- sr)
  sr--preserves-NonTrivial =
    SemiRotationElim.elimProp (\sr -> isPropΠ (\_ -> isProp-NonTrivialSemiRotation (- sr))) f
    where
    f : (r : Rotation) -> NonTrivialSemiRotation' r -> NonTrivialSemiRotation' (r- r)
    f r (non-trivial-semi-rotation r#0 r#h) = (non-trivial-semi-rotation -r#0 -r#h)
      where
      -r#0 : (- r) # 0#
      -r#0 = subst ((- r) #_) minus-zero (minus-preserves-r# r#0)
      -r#h : (- r) # half-rotation
      -r#h = subst ((- r) #_) minus-half-rotation (minus-preserves-r# r#h)

  record _sr#_ (sr1 sr2 : SemiRotation) : Type₁ where
    no-eta-equality ; pattern
    constructor sr#-cons
    field
      nt : NonTrivialSemiRotation (diff sr1 sr2)

abstract

  +-reflects-sr# : {sr1 sr2 sr3 sr4 : SemiRotation} ->
    (sr1 + sr2) sr# (sr3 + sr4) -> ∥ (sr1 sr# sr3) ⊎ (sr2 sr# sr4) ∥
  +-reflects-sr# {sr1} {sr2} {sr3} {sr4} (sr#-cons nt) =
    ∥-map (⊎-map sr#-cons sr#-cons) (sr+-reflects-NonTrivial (diff sr1 sr3) (diff sr2 sr4) nt')
    where
    nt' : NonTrivialSemiRotation ((diff sr1 sr3) + (diff sr2 sr4))
    nt' = subst NonTrivialSemiRotation (sym (+-swap-diffᵉ sr1 sr3 sr2 sr4)) nt

  +-reflects-sr#0 : {sr1 sr2 : SemiRotation} -> (sr1 + sr2) sr# 0# -> ∥ (sr1 sr# 0#) ⊎ (sr2 sr# 0#) ∥
  +-reflects-sr#0 {sr1} {sr2} r1r2#0 =
    +-reflects-sr# (subst ((sr1 + sr2) sr#_) (sym +-right-zero) r1r2#0)


  minus-preserves-sr# : {sr1 sr2 : SemiRotation} -> sr1 sr# sr2 -> (- sr1) sr# (- sr2)
  minus-preserves-sr# {sr1} {sr2} (sr#-cons nt) =
    sr#-cons (subst NonTrivialSemiRotation (minus-distrib-plusᵉ sr2 (- sr1))
                    (sr--preserves-NonTrivial (diff sr1 sr2) nt))

  sr#->r# : {r1 r2 : Rotation} -> [ r1 ] sr# [ r2 ] -> (r1 # r2) × (r1 # add-half-rotation r2)
  sr#->r# (sr#-cons (non-trivial-semi-rotation 12#0 12#h)) =
    subst2 _#_ +-left-zero (+-assoc >=> (+-right (+-commute >=> +-inverse)) >=> +-right-zero)
           (+₂-preserves-r# (sym-# 12#0)) ,
    subst2 _#_ (+-right (sym diff-anticommute) >=> diff-step)
               (+-right minus-half-rotation >=> sym (add-half-rotation-path _))
               (+₁-preserves-r# (minus-preserves-r# 12#h))


abstract
  isProp-sr# : {sr1 sr2 : SemiRotation} -> isProp (sr1 sr# sr2)
  isProp-sr# {sr1} {sr2} (sr#-cons nt1) (sr#-cons nt2) =
    cong sr#-cons (isProp-NonTrivialSemiRotation (diff sr1 sr2) nt1 nt2)

  private

    sym-sr# : Symmetric _sr#_
    sym-sr# {sr1} {sr2} (sr#-cons nt) =
      sr#-cons (subst NonTrivialSemiRotation p (sr--preserves-NonTrivial (diff sr1 sr2) nt))
      where
      p : - (diff sr1 sr2) == diff sr2 sr1
      p = sym (diff-anticommuteᵉ sr2 sr1)

    irrefl-sr# : Irreflexive _sr#_
    irrefl-sr# {sr} (sr#-cons nt) =
      ¬NonTrivial-zero-semi-rotation (subst NonTrivialSemiRotation (+-inverseᵉ sr) nt)

    comparison-sr# : (sr1 sr2 sr3 : SemiRotation) -> (sr1 sr# sr3) ->
                     ∥ (sr1 sr# sr2) ⊎ (sr2 sr# sr3) ∥
    comparison-sr# sr1 sr2 sr3 (sr#-cons nt) =
      ∥-map (⊎-map sr#-cons sr#-cons)
        (sr+-reflects-NonTrivial (diff sr1 sr2) (diff sr2 sr3)
          (subst NonTrivialSemiRotation (sym (diff-transᵉ sr1 sr2 sr3)) nt))

    tight-sr# : Tight _sr#_
    tight-sr# {sr1} {sr2} ¬sr1#sr2 = sym path
      where
      ¬nt : ¬ (NonTrivialSemiRotation (diff sr1 sr2))
      ¬nt = ¬sr1#sr2 ∘ sr#-cons

      diff-path : (diff sr1 sr2) == zero-semi-rotation
      diff-path = ¬NonTrivial->zero-semi-rotation ¬nt

      path : sr2 == sr1
      path =
        sym +-left-zero >=>
        (+-commuteᵉ zero-semi-rotation sr2) >=>
        cong (sr2 +_) (sym (+-inverseᵉ sr1) >=> +-commuteᵉ sr1 (- sr1)) >=>
        sym (+-assocᵉ sr2 (- sr1) sr1) >=>
        cong (_+ sr1) diff-path
        >=> +-left-zero

instance
  isTightApartness-sr# : isTightApartness _sr#_
  isTightApartness-sr# = record
    { tight-# = tight-sr#
    ; irrefl-# = irrefl-sr#
    ; sym-# = sym-sr#
    ; comparison-# = comparison-sr#
    ; isProp-# = isProp-sr#
    }
