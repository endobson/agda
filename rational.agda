{-# OPTIONS --cubical --safe --exact-split #-}

module rational where

open import abs
open import additive-group
open import additive-group.instances.int
open import apartness
open import apartness.discrete
open import base
open import discrete
open import equality
open import fin
open import functions
open import funext
open import hlevel
open import int
open import isomorphism
open import nat
open import nat.exponentiation
open import nat.order
open import relation
open import ring
open import ring.implementations.int
open import semiring
open import semiring.exponentiation
open import set-quotient
open import sigma.base
open import truncation
open import univalence

import solver
open solver using (_⊗_ ; _⊕_)

record ℚ' : Type₀ where
  constructor ℚ'-cons
  field
    numerator : Int
    denominator : Int
    NonZero-denominator : NonZero denominator


private
  numer : ℚ' -> Int
  numer = ℚ'.numerator
  denom : ℚ' -> Int
  denom = ℚ'.denominator
  rNonZero : (r : ℚ') -> NonZero (denom r)
  rNonZero = ℚ'.NonZero-denominator

Discrete-ℚ' : Discrete ℚ'
Discrete-ℚ' q1@(ℚ'-cons n1 d1 nz1) q2@(ℚ'-cons n2 d2 nz2) =
  handle (discreteInt n1 n2) (discreteInt d1 d2)
  where
  handle : Dec (n1 == n2) -> Dec (d1 == d2) -> Dec (q1 == q2)
  handle (no n1!=n2) _ =
    no (n1!=n2 ∘ (cong numer))
  handle (yes n1=n2) (no d1!=d2) =
    no (d1!=d2 ∘ (cong denom))
  handle (yes n1=n2) (yes d1=d2) =
    yes (\i -> (ℚ'-cons (n1=n2 i) (d1=d2 i)
                        (isProp->PathPᵉ (\i -> int.isPropNonZero {d1=d2 i}) nz1 nz2 i)))

_r~_ : Rel ℚ' ℓ-zero
_r~_ a b = (numer a) * (denom b) == (numer b) * (denom a)

record _r~'_ (a : ℚ') (b : ℚ') : Type₀ where
  field
    path : a r~ b

r~'->r~ : {a b : ℚ'} -> a r~' b -> a r~ b
r~'->r~ v = _r~'_.path v

r~->r~' : {a b : ℚ'} -> a r~ b -> a r~' b
r~->r~' {a} {b} v = record { path = v }

ℚᵉ : Type₀
ℚᵉ = ℚ' / _r~_

opaque
  ℚ : Type₀
  ℚ = ℚᵉ

  ℚ'->ℚ : ℚ' -> ℚ
  ℚ'->ℚ q' = [ q' ]

  ℚ-eval : ℚ == ℚᵉ
  ℚ-eval = refl

  r~->path : (a b : ℚ') -> (a r~ b) -> (ℚ'->ℚ a) == (ℚ'->ℚ b)
  r~->path a b r = eq/ a b r

trans-r~ : (a b c : ℚ') -> a r~ b -> b r~ c -> a r~ c
trans-r~ a b c p1 p2 = int.*-right-injective (rNonZero b) p3
  where
  na = numer a
  nb = numer b
  nc = numer c
  da = denom a
  db = denom b
  dc = denom c

  p3 : (na * dc) * db == (nc * da) * db
  p3 = *-left *-commute >=> *-assoc >=> cong (dc *_) p1 >=>
       sym *-assoc >=> *-left (*-commute >=> p2) >=>
       *-assoc >=> *-right *-commute >=> sym *-assoc

refl-r~ : (a : ℚ') -> a r~ a
refl-r~ a = refl

sym-r~ : (a b : ℚ') -> a r~ b -> b r~ a
sym-r~ a b a~b = sym a~b

path->r~ : {a b : ℚ'} -> a == b -> a r~ b
path->r~ {a} p = subst (a r~_) p (refl-r~ a)

path->r~' : {a b : ℚ'} -> a == b -> a r~' b
path->r~' p = r~->r~' (path->r~ p)


trans-r~' : {a b c : ℚ'} -> a r~' b -> b r~' c -> a r~' c
trans-r~' {a} {b} {c} p1 p2 = r~->r~' (trans-r~ a b c (r~'->r~ p1) (r~'->r~ p2))

isEquivRel-r~ : isEquivRel _r~_
isEquivRel-r~ = record
  { reflexive = \{a} -> refl-r~ a
  ; symmetric = \{a} {b} -> sym-r~ a b
  ; transitive = \{a} {b} {c} -> trans-r~ a b c
  }

isProp-r~ : isPropValued _r~_
isProp-r~ _ _ = isSetInt _ _

Decidable2-r~ : Decidable2 _r~_
Decidable2-r~ q r = discreteInt _ _

nd-paths->path : (a b : ℚ') -> (numer a == numer b) -> (denom a == denom b) -> a == b
nd-paths->path a b pn pd = (\i -> record
  { numerator = pn i
  ; denominator = pd i
  ; NonZero-denominator = pnz i
  })
  where
  pnz : PathP (\i -> NonZero (pd i)) (rNonZero a) (rNonZero b)
  pnz = isProp->PathP (\_ -> int.isPropNonZero)

isSet-ℚᵉ : isSet ℚᵉ
isSet-ℚᵉ = squash/

opaque
  unfolding ℚ

  isSetℚ : isSet ℚ
  isSetℚ = isSet-ℚᵉ

  Discrete-ℚ : Discrete ℚ
  Discrete-ℚ = Discrete-SetQuotient isProp-r~ isEquivRel-r~ Decidable2-r~

instance
  isTightApartness-ℚ# : isTightApartness (\ (x y : ℚ) -> x != y)
  isTightApartness-ℚ# = isTightApartness-!= Discrete-ℚ

_r+'ᵉ_ : ℚ' -> ℚ' -> ℚ'
a r+'ᵉ b = record
  { numerator = ((numer a) * (denom b)) + ((numer b) * (denom a))
  ; denominator = (denom a) * (denom b)
  ; NonZero-denominator = int.*-NonZero-NonZero (rNonZero a) (rNonZero b)
  }

opaque
  _r+'_ : ℚ' -> ℚ' -> ℚ'
  a r+' b = a r+'ᵉ b

  r+'-eval : {a b : ℚ'} -> a r+' b == a r+'ᵉ b
  r+'-eval = refl

  r+'-commute : (a b : ℚ') -> a r+' b == b r+' a
  r+'-commute a b = nd-paths->path ab ba n-p d-p
    where
    ab ba : ℚ'
    na nb da db : ℤ
    ab = a r+' b
    ba = b r+' a
    na = numer a
    nb = numer b
    da = denom a
    db = denom b

    n-p : numer ab == numer ba
    n-p = +-commute -- {na * db} {nb * da}

    d-p : denom ab == denom ba
    d-p = *-commute -- {da} {db}


  r+'-preserves-r~₂ : (a b1 b2 : ℚ') -> b1 r~ b2 -> (a r+' b1) r~ (a r+' b2)
  r+'-preserves-r~₂ a b1 b2 r = path
    where
    path'1 : (nx dx ny dy nz dz : Int) ->
      (((nx * dy) + (ny * dx)) * (dx * dz))
      ==
      ((nx * dx) * (dy * dz)) + ((dx * dx) * (ny * dz))
    path'1 =
      solver.IntSolver.solve 6
      (\ nx dx ny dy nz dz ->
         ((((nx ⊗ dy) ⊕ (ny ⊗ dx)) ⊗ (dx ⊗ dz)) ,
          ((nx ⊗ dx) ⊗ (dy ⊗ dz)) ⊕ ((dx ⊗ dx) ⊗ (ny ⊗ dz))))
      refl

    path'2 : (nx dx ny dy nz dz : Int) ->
      (((nx * dz) + (nz * dx)) * (dx * dy))
      ==
      ((nx * dx) * (dy * dz)) + ((dx * dx) * (nz * dy))
    path'2 =
      solver.IntSolver.solve 6
      (\ nx dx ny dy nz dz ->
         ((((nx ⊗ dz) ⊕ (nz ⊗ dx)) ⊗ (dx ⊗ dy)) ,
          ((nx ⊗ dx) ⊗ (dy ⊗ dz)) ⊕ ((dx ⊗ dx) ⊗ (nz ⊗ dy))))
      refl

    path :
      ((((numer a) * (denom b1)) + ((numer b1) * (denom a))) * ((denom a) *
      (denom b2)))
      ==
      ((((numer a) * (denom b2)) + ((numer b2) * (denom a))) *
       ((denom a) * (denom b1)))
    path =
      path'1 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2)
      >=> cong ((((numer a) * (denom a)) * ((denom b1) * (denom b2))) +_)
               (cong (((denom a) * (denom a)) *_) r)
      >=> sym (path'2 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))

  r+'-preserves-r~₁ : (b a1 a2 : ℚ') -> a1 r~ a2 -> (a1 r+' b) r~ (a2 r+' b)
  r+'-preserves-r~₁ b a1 a2 r =
    transport (\i -> (r+'-commute b a1 i) r~ (r+'-commute b a2 i)) (r+'-preserves-r~₂ b a1 a2 r)


same-denom-r+' : (a b : ℚ') -> ℚ'
same-denom-r+' a b = record
  { numerator = numer a + numer b
  ; denominator = denom a
  ; NonZero-denominator = rNonZero a
  }

opaque
  unfolding _r+'_

  same-denom-r+'-r~ : (a b : ℚ') -> denom a == denom b -> same-denom-r+' a b r~ (a r+' b)
  same-denom-r+'-r~ a b p =
   *-distrib-+-right >=>
   cong2 _+_ (*-right *-commute >=> sym *-assoc)
             (*-right (*-right (sym p)) >=> sym *-assoc) >=>
   sym *-distrib-+-right


_r+ᵉ_ : ℚᵉ -> ℚᵉ -> ℚᵉ
_r+ᵉ_ = SetQuotientElim.rec2 squash/
          (\a b -> [ a r+' b ])
          (\a1 a2 b r -> eq/ _ _ (r+'-preserves-r~₁ b a1 a2 r))
          (\a b1 b2 r -> eq/ _ _ (r+'-preserves-r~₂ a b1 b2 r))


opaque
  unfolding ℚ

  _r+_ : ℚ -> ℚ -> ℚ
  _r+_ = _r+ᵉ_

  r+-eval : {a b : ℚ'} -> (ℚ'->ℚ a) r+ (ℚ'->ℚ b) == (ℚ'->ℚ (a r+' b))
  r+-eval = refl

  r+-commute : (a b : ℚ) -> (a r+ b) == (b r+ a)
  r+-commute = SetQuotientElim.elimProp2 (\a b -> isSetℚ _ _) (\a b -> cong [_] (r+'-commute a b))

0r' : ℚ'
0r' = record
  { numerator = (int 0)
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

opaque
  unfolding _r+'_

  r+'-left-zero : (a : ℚ') -> (0r' r+' a) == a
  r+'-left-zero a = nd-paths->path 0a a pn pd
    where
    na da : ℤ
    na = numer a
    da = denom a
    0a : ℚ'
    0a = (0r' r+' a)


    pn' : ((int 0) * (denom a)) + ((numer a) * (int 1)) == (numer a)
    pn' = cong (_+ ((numer a) * (int 1))) *-left-zero
          >=> +-left-zero
          >=> *-right-one

    pn : (numer 0a) == (numer a)
    pn = pn'

    pd : (denom 0a) == (denom a)
    pd = *-left-one

  r+'-right-zero : (a : ℚ') -> (a r+' 0r') == a
  r+'-right-zero a = r+'-commute a 0r' >=> r+'-left-zero a

0r : ℚ
0r = ℚ'->ℚ 0r'

opaque
  unfolding _r+_

  r+-left-zero : (a : ℚ) -> (0r r+ a) == a
  r+-left-zero = SetQuotientElim.elimProp (\a -> isSetℚ _ _) (\a -> cong [_] (r+'-left-zero a))

  r+-right-zero : (a : ℚ) -> (a r+ 0r) == a
  r+-right-zero a = r+-commute a 0r >=> r+-left-zero a

_r*'_ : ℚ' -> ℚ' -> ℚ'
a r*' b = record
  { numerator = (numer a) * (numer b)
  ; denominator = (denom a) * (denom b)
  ; NonZero-denominator = int.*-NonZero-NonZero (rNonZero a) (rNonZero b)
  }

r*'-commute : (a b : ℚ') -> a r*' b == b r*' a
r*'-commute a b = nd-paths->path ab ba n-p d-p
  where
  ab = a r*' b
  ba = b r*' a
  na = numer a
  nb = numer b
  da = denom a
  db = denom b

  n-p : numer ab == numer ba
  n-p = *-commute -- {na} {nb}

  d-p : denom ab == denom ba
  d-p = *-commute -- {da} {db}


private
  r*'-preserves-r~₂ : (a b1 b2 : ℚ') -> b1 r~ b2 -> (a r*' b1) r~ (a r*' b2)
  r*'-preserves-r~₂ a b1 b2 r = path
    where
    ab1 = a r*' b1
    ab2 = a r*' b2

    path1 : (nx dx ny dy nz dz : Int) ->
      (nx * ny) * (dx * dz) == (nx * dx) * (ny * dz)
    path1 = solver.IntSolver.solve 6
            (\ nx dx ny dy nz dz  ->
               (nx ⊗ ny) ⊗ (dx ⊗ dz) , (nx ⊗ dx) ⊗ (ny ⊗ dz)) refl

    path2 : (nx dx ny dy nz dz : Int) ->
      (nx * nz) * (dx * dy) == (nx * dx) * (nz * dy)
    path2 = solver.IntSolver.solve 6
            (\ nx dx ny dy nz dz  ->
               (nx ⊗ nz) ⊗ (dx ⊗ dy) , (nx ⊗ dx) ⊗ (nz ⊗ dy)) refl

    path : (numer ab1) * (denom ab2) == (numer ab2) * (denom ab1)
    path = (path1 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))
           >=> cong (((numer a) * (denom a)) *_) r
           >=> sym (path2 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))

  r*'-preserves-r~₁ : (b a1 a2 : ℚ') -> a1 r~ a2 -> (a1 r*' b) r~ (a2 r*' b)
  r*'-preserves-r~₁ b a1 a2 r =
    transport (\i -> (r*'-commute b a1 i) r~ (r*'-commute b a2 i)) (r*'-preserves-r~₂ b a1 a2 r)

_r*ᵉ_ : ℚᵉ -> ℚᵉ -> ℚᵉ
_r*ᵉ_ = SetQuotientElim.rec2 squash/
          (\a b -> [ a r*' b ])
          (\a1 a2 b r -> eq/ _ _ (r*'-preserves-r~₁ b a1 a2 r))
          (\a b1 b2 r -> eq/ _ _ (r*'-preserves-r~₂ a b1 b2 r))

opaque
  unfolding ℚ

  _r*_ : ℚ -> ℚ -> ℚ
  _r*_ = _r*ᵉ_

  r*-eval : {a b : ℚ'} -> (ℚ'->ℚ a) r* (ℚ'->ℚ b) == (ℚ'->ℚ (a r*' b))
  r*-eval = refl

  r*-commute : (a b : ℚ) -> (a r* b) == (b r* a)
  r*-commute = SetQuotientElim.elimProp2 (\a b -> isSetℚ _ _) (\a b -> cong [_] (r*'-commute a b))

  private
    r*'-left-zero : (a : ℚ') -> (0r' r*' a) r~ 0r'
    r*'-left-zero a = *-right-one >=> *-left-zero >=> sym (*-left-zero)

  r*-left-zero : (a : ℚ) -> (0r r* a) == 0r
  r*-left-zero = SetQuotientElim.elimProp (\a -> isSetℚ _ _) (\a -> eq/ _ _ (r*'-left-zero a))

  r*-right-zero : (a : ℚ) -> (a r* 0r) == 0r
  r*-right-zero a = r*-commute a 0r >=> r*-left-zero a

1r' : ℚ'
1r' = record
  { numerator = (int 1)
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

1r : ℚ
1r = ℚ'->ℚ 1r'

private
  r*'-left-one : (a : ℚ') -> (1r' r*' a) == a
  r*'-left-one a = nd-paths->path _ _ (*-left-oneᵉ (numer a)) (*-left-oneᵉ (denom a))

opaque
  unfolding _r*_

  r*-left-one : (a : ℚ) -> (1r r* a) == a
  r*-left-one = SetQuotientElim.elimProp (\a -> isSetℚ _ _) (\a -> cong [_] (r*'-left-one a))

  r*-right-one : (a : ℚ) -> (a r* 1r) == a
  r*-right-one a = r*-commute a 1r >=> r*-left-one a

private
  r*'-assoc : (a b c : ℚ') -> ((a r*' b) r*' c) == (a r*' (b r*' c))
  r*'-assoc a b c = nd-paths->path _ _ (*-assocᵉ (numer a) (numer b) (numer c))
                                       (*-assocᵉ (denom a) (denom b) (denom c))

opaque
  unfolding _r*_

  r*-assoc : (a b c : ℚ) -> ((a r* b) r* c) == (a r* (b r* c))
  r*-assoc = SetQuotientElim.elimProp3 (\a b c -> isSetℚ _ _) (\a b c -> cong [_] (r*'-assoc a b c))

opaque
  unfolding _r+'_

  r+'-assoc : {a b c : ℚ'} -> ((a r+' b) r+' c) r~ (a r+' (b r+' c))
  r+'-assoc {a} {b} {c} = path
    where
    na nb nc da db dc : ℤ
    na = numer a
    nb = numer b
    nc = numer c
    da = denom a
    db = denom b
    dc = denom c

    path : ((((na * db) + (nb * da)) * dc) + (nc * (da * db)))
           * (da * (db * dc))
           ==
           ((na * (db * dc)) + (((nb * dc) + (nc * db)) * da))
           * ((da * db) * dc)
    path = solver.IntSolver.solve 6
           (\ na da nb db nc dc ->
              ((((na ⊗ db) ⊕ (nb ⊗ da)) ⊗ dc) ⊕ (nc ⊗ (da ⊗ db))) ⊗ (da ⊗ (db ⊗ dc)) ,
              ((na ⊗ (db ⊗ dc)) ⊕ (((nb ⊗ dc) ⊕ (nc ⊗ db)) ⊗ da)) ⊗ ((da ⊗ db) ⊗ dc))
           refl na da nb db nc dc

  r+'-assoc' : {a b c : ℚ'} -> ((a r+' b) r+' c) r~' (a r+' (b r+' c))
  r+'-assoc' {a} {b} {c} = r~->r~' (r+'-assoc {a} {b} {c})

opaque
  unfolding _r+_

  r+-assoc : (a b c : ℚ) -> ((a r+ b) r+ c) == (a r+ (b r+ c))
  r+-assoc = SetQuotientElim.elimProp3
               (\a b c -> isSetℚ ((a r+ b) r+ c) (a r+ (b r+ c)))
               (\a b c -> (eq/ ((a r+' b) r+' c) (a r+' (b r+' c)) (r+'-assoc {a} {b} {c})))

opaque
  unfolding _r+'_

  r*'-distrib-r+'-right : (a b c : ℚ') -> ((a r+' b) r*' c) r~ ((a r*' c) r+' (b r*' c))
  r*'-distrib-r+'-right a b c = path
    where
    ab ac bc ab-c ac-bc : ℚ'
    na nb nc da db dc : ℤ

    ab = a r+' b
    ac = a r*' c
    bc = b r*' c
    ab-c = ab r*' c
    ac-bc = ac r+' bc
    na = numer a
    nb = numer b
    nc = numer c
    da = denom a
    db = denom b
    dc = denom c

    path : (((na * db) + (nb * da)) * nc) * ((da * dc) * (db * dc))
           == (((na * nc) * (db * dc)) + ((nb * nc) * (da * dc))) * ((da * db) * dc)
    path = solver.IntSolver.solve 6
           (\ na da nb db nc dc ->
              (((na ⊗ db) ⊕ (nb ⊗ da)) ⊗ nc) ⊗ ((da ⊗ dc) ⊗ (db ⊗ dc)) ,
              (((na ⊗ nc) ⊗ (db ⊗ dc)) ⊕ ((nb ⊗ nc) ⊗ (da ⊗ dc))) ⊗ ((da ⊗ db) ⊗ dc))
           refl na da nb db nc dc

opaque
  unfolding _r*_ _r+_

  r*-distrib-r+-right : (a b c : ℚ) -> ((a r+ b) r* c) == ((a r* c) r+ (b r* c))
  r*-distrib-r+-right =
    SetQuotientElim.elimProp3 (\a b c -> isSetℚ _ _)
                           (\a b c -> (eq/ _ _ (r*'-distrib-r+'-right a b c)))


r-' : ℚ' -> ℚ'
r-' a = record
  { numerator = - (ℚ'.numerator a)
  ; denominator = ℚ'.denominator a
  ; NonZero-denominator = ℚ'.NonZero-denominator a
  }

opaque
  r-'-preserves-r~ : (a1 a2 : ℚ') -> a1 r~ a2 -> (r-' a1) r~ (r-' a2)
  r-'-preserves-r~ a1 a2 r =
    minus-extract-left >=> cong -_ r >=> sym minus-extract-left
    where
    na1 da1 na2 da2 : ℤ
    na1 = numer a1
    da1 = denom a1
    na2 = numer a2
    da2 = denom a2

opaque
  unfolding _r+'_

  r-'-distrib-r+' : (a b : ℚ') -> r-' (a r+' b) == (r-' a) r+' (r-' b)
  r-'-distrib-r+' a b = nd-paths->path _ _ path refl
    where
    na da nb db : ℤ
    na = numer a
    da = denom a
    nb = numer b
    db = denom b
    path : (- ((na * db) + (nb * da))) == (((- na) * db) + ((- nb) * da))
    path = int.minus-distrib-+ >=> cong2 _+_ (sym minus-extract-left) (sym minus-extract-left)

  r-'-double-inverse : (a : ℚ') -> r-' (r-' a) == a
  r-'-double-inverse _ = nd-paths->path _ _ minus-double-inverse refl


opaque
  unfolding _r+'_

  r+'-inverse : (a : ℚ') -> (a r+' (r-' a)) r~ 0r'
  r+'-inverse a =
    *-right-one
    >=> sym (*-distrib-+-right)
    >=> cong (_* da) (int.add-minus-zero {na})
    >=> *-left-zero
    >=> sym *-left-zero
    where
    na da : ℤ
    na = numer a
    da = denom a


r-ᵉ_ : ℚᵉ -> ℚᵉ
r-ᵉ_ = SetQuotientElim.rec isSet-ℚᵉ
       (\a -> [ r-' a ])
       (\a1 a2 r -> eq/ _ _ (r-'-preserves-r~ a1 a2 r))

opaque
  unfolding ℚ

  r-_ : ℚ -> ℚ
  r- x = r-ᵉ x

opaque
  unfolding _r+_ r-_

  r+-inverse : (a : ℚ) -> (a r+ (r- a)) == 0r
  r+-inverse = SetQuotientElim.elimProp
               (\_ -> isSetℚ _ _)
               (\a -> eq/ _ _ (r+'-inverse a))

opaque
  unfolding _r*_ r-_

  r*-minus-extract-left : (a1 a2 : ℚ) -> (r- a1) r* a2 == r- (a1 r* a2)
  r*-minus-extract-left =
    SetQuotientElim.elimProp2
      (\_ _ -> isSetℚ _ _)
      (\a1 a2 -> cong [_] (nd-paths->path _ _ minus-extract-left refl))

  r*-minus-extract-right : (a1 a2 : ℚ) -> a1 r* (r- a2) == r- (a1 r* a2)
  r*-minus-extract-right a1 a2 = r*-commute a1 (r- a2) >=> r*-minus-extract-left a2 a1 >=>
                                 cong r-_ (r*-commute a2 a1)

instance
  AdditiveCommMonoid-ℚ : AdditiveCommMonoid ℚ
  AdditiveCommMonoid-ℚ = record
    { comm-monoid = record
      { monoid = record
        { ε = 0r
        ; _∙_ = _r+_
        ; ∙-assoc = \ {m} {n} {o} -> r+-assoc m n o
        ; ∙-left-ε = \ {n} -> r+-left-zero n
        ; ∙-right-ε = \ {n} -> r+-right-zero n
        ; isSet-Domain = isSetℚ
        }
      ; ∙-commute = \ {m} {n} -> r+-commute m n
      }
    }

  AdditiveGroup-ℚ : AdditiveGroup AdditiveCommMonoid-ℚ
  AdditiveGroup-ℚ = record
    { -_ = r-_
    ; +-inverse = (\ {a} -> r+-inverse a)
    }

  Semiring-ℚ : Semiring AdditiveCommMonoid-ℚ
  Semiring-ℚ = record
    { 1# = 1r
    ; _*_ = _r*_
    ; *-assoc = (\ {m} {n} {o} -> (r*-assoc m n o))
    ; *-commute = (\ {m} {n} -> (r*-commute m n))
    ; *-left-zero = (\ {n} -> r*-left-zero n)
    ; *-left-one = (\ {n} -> r*-left-one n)
    ; *-distrib-+-right = (\ {m} {n} {o} -> r*-distrib-r+-right m n o)
    ; isSet-Domain = isSetℚ
    }

  Ring-ℚ : Ring Semiring-ℚ AdditiveGroup-ℚ
  Ring-ℚ = record {}


ℚInv' : Pred ℚ' ℓ-zero
ℚInv' a = NonZero (numer a)

isProp-ℚInv' : {a : ℚ'} -> isProp (ℚInv' a)
isProp-ℚInv' = int.isPropNonZero

r1/' : (a : ℚ') -> ℚInv' a -> ℚ'
r1/' a i = record
  { numerator = ℚ'.denominator a
  ; denominator = ℚ'.numerator a
  ; NonZero-denominator = i
  }

opaque
  r1/'-preserves-r~ : (a1 a2 : ℚ') -> (i1 : ℚInv' a1) -> (i2 : ℚInv' a2) -> a1 r~ a2 ->
                      (r1/' a1 i1) r~ (r1/' a2 i2)
  r1/'-preserves-r~ a1 a2 _ _ r = *-commute >=> sym r >=> *-commute


  r1/'-inverse : (a : ℚ') -> (i : ℚInv' a) -> ((r1/' a i) r*' a) r~ 1r'
  r1/'-inverse a i = path
    where
    path : ((denom a) * (numer a)) * (int 1) == (int 1) * ((numer a) * (denom a))
    path = *-right-one >=> *-commute >=> sym *-left-one


  r1/'-double-inverse : (a : ℚ') -> (i1 : ℚInv' a) -> (i2 : ℚInv' (r1/' a i1)) ->
                        r1/' (r1/' a i1) i2 == a
  r1/'-double-inverse a _ _ = nd-paths->path _ _ refl refl

ℚInv : Pred ℚ ℓ-zero
ℚInv a = (a != 0r)

isProp-ℚInv : {a : ℚ} -> isProp (ℚInv a)
isProp-ℚInv = isProp¬


opaque
  unfolding ℚ

  ℚInv->ℚInv' : (a : ℚ') -> ℚInv (ℚ'->ℚ a) -> ℚInv' a
  ℚInv->ℚInv' a i = handle (numer a) refl
    where
    handle : (x : Int) -> (x == numer a) -> ℚInv' a
    handle (int.nonneg (suc _)) p = subst NonZero p (inj-l tt)
    handle (int.neg _) p = subst NonZero p (inj-r tt)
    handle (int.nonneg zero) p = bot-elim (i (eq/ a 0r' path))
      where
      path : a r~ 0r'
      path = *-right-one >=> sym p >=> sym *-left-zero


-- TODO get this back to computing
opaque
  unfolding ℚ

  r1/ᵉ : (a : ℚ) -> (ℚInv a) -> ℚ
  r1/ᵉ = SetQuotientElim.elim
           (\_ -> isSetΠ (\_ -> isSetℚ))
           g
           (\a1 a2 r -> funExtDep a1 a2 (\i1 i2 ->
             eq/ (r1/' a1 (ℚInv->ℚInv' a1 i1)) (r1/' a2 (ℚInv->ℚInv' a2 i2))
                 (r1/'-preserves-r~ a1 a2 (ℚInv->ℚInv' a1 i1) (ℚInv->ℚInv' a2 i2) r)))
    where
    g : (a : ℚ') -> ℚInv (ℚ'->ℚ a) -> ℚ
    g a i = ℚ'->ℚ (r1/' a (ℚInv->ℚInv' a i))


opaque
  unfolding ℚ r1/ᵉ _r*_

  r1/ : (a : ℚ) -> (ℚInv a) -> ℚ
  r1/ = r1/ᵉ

  r1/-eval : {a : ℚ} -> {i : (ℚInv a)} -> (r1/ a i) == (r1/ᵉ a i)
  r1/-eval = refl

  r1/-inverse : (a : ℚ) -> (i : ℚInv a) -> ((r1/ a i) r* a) == 1r
  r1/-inverse = SetQuotientElim.elimProp
                 (\_ -> isPropΠ (\_ -> isSetℚ _ _))
                 (\ a i -> eq/ _ _ (r1/'-inverse a (ℚInv->ℚInv' _ i)))

  r1/-double-inverse : (a : ℚ) -> (i1 : ℚInv a) -> (i2 : ℚInv (r1/ a i1)) ->
                       r1/ (r1/ a i1) i2 == a
  r1/-double-inverse =
    SetQuotientElim.elimProp
      (\_ -> isPropΠ2 (\_ _ -> isSetℚ _ _))
      (\ a i1 i2 -> cong [_] (r1/'-double-inverse a (ℚInv->ℚInv' _ i1) (ℚInv->ℚInv' _ i2)))

r1/-distrib-* : (a b : ℚ) (ai : ℚInv a) (bi : ℚInv b) (abi : ℚInv (a * b)) ->
                r1/ (a * b) abi == (r1/ a ai) * (r1/ b bi)
r1/-distrib-* a b ai bi abi =
  sym *-right-one >=>
  *-right (sym *-right-one >=>
           cong2 _*_ (sym (r1/-inverse a ai)) (sym (r1/-inverse b bi)) >=>
           *-assoc >=> (*-right (*-commute >=> *-assoc)) >=> sym *-assoc >=>
           *-right *-commute >=> *-commute) >=>
  sym *-assoc >=>
  *-left (r1/-inverse (a * b) abi) >=>
  *-left-one




ℤ->ℚ' : Int -> ℚ'
ℤ->ℚ' x = record
  { numerator = x
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

ℤ->ℚ : Int -> ℚ
ℤ->ℚ x = ℚ'->ℚ (ℤ->ℚ' x)

ℕ->ℚ' : Nat -> ℚ'
ℕ->ℚ' n = ℤ->ℚ' (ℕ->ℤ n)

ℕ->ℚ : Nat -> ℚ
ℕ->ℚ n = ℤ->ℚ (ℕ->ℤ n)


opaque
  unfolding _r+_ _r+'_

  ℤ->ℚ-preserves-+ : (x y : Int) -> ℤ->ℚ (x + y) == ℤ->ℚ x r+ ℤ->ℚ y
  ℤ->ℚ-preserves-+ x y = eq/ _ _ r
    where
    r1 : (x + y) * ((int 1) * (int 1)) == (x + y)
    r1 = cong ((x + y) *_) *-right-one >=> *-right-one

    r2 : ((x * (int 1)) + (y * (int 1))) * (int 1) == (x + y)
    r2 = *-right-one >=> cong2 _+_ *-right-one  *-right-one

    r : (x + y) * ((int 1) * (int 1)) == ((x * (int 1)) + (y * (int 1))) * (int 1)
    r = r1 >=> sym r2

opaque
  unfolding _r*_

  ℤ->ℚ-preserves-* : (x y : Int) -> ℤ->ℚ (x * y) == ℤ->ℚ x r* ℤ->ℚ y
  ℤ->ℚ-preserves-* x y = cong [_] (nd-paths->path _ _ refl (sym *-left-one))


opaque
  unfolding r-_

  ℤ->ℚ-preserves-minus : (x : Int) -> ℤ->ℚ (- x) == r- (ℤ->ℚ x)
  ℤ->ℚ-preserves-minus x = cong [_] refl

ℤ->ℚ-preserves-diff : (x y : ℤ) -> ℤ->ℚ (diff x y) == diff (ℤ->ℚ x) (ℤ->ℚ y)
ℤ->ℚ-preserves-diff x y =
  ℤ->ℚ-preserves-+ y (- x) >=> +-right (ℤ->ℚ-preserves-minus x)

private
  ℚ'->split-ℤ : (q' : ℚ') -> Σ[ n ∈ ℤ ] Σ[ d ∈ ℤ ] (NonZero d × (ℤ->ℚ' n r~ (q' r*' ℤ->ℚ' d)))
  ℚ'->split-ℤ (ℚ'-cons n d nz-d) = n , d , (nz-d , sym *-assoc)

  private
    Pos'-abs'-d : {d : ℤ} -> NonZero d -> Pos' (abs' d)
    Pos'-abs'-d {nonneg zero}    (inj-l ())
    Pos'-abs'-d {nonneg zero}    (inj-r ())
    Pos'-abs'-d {nonneg (suc n)} _ = tt
    Pos'-abs'-d {neg n}          _ = tt


  ℚ'->split-ℤℕ⁺ : (q' : ℚ') -> Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] ((ℤ->ℚ' n r~ (q' r*' ℕ->ℚ' ⟨ d ⟩)))
  ℚ'->split-ℤℕ⁺ (ℚ'-cons n d nz@(inj-l pos-d)) =
    n , (abs' d , Pos'-abs'-d nz) , *-right (*-left (nonneg-abs' d (inj-l pos-d))) >=> sym *-assoc
  ℚ'->split-ℤℕ⁺ (ℚ'-cons n d nz@(inj-r neg-d)) = - n , (abs' d , Pos'-abs'-d nz) , p
    where
    p = minus-extract-left >=>
        sym minus-extract-right >=>
        *-right (sym minus-extract-left >=>
                 *-left (cong -_ (nonpos-abs' d (inj-l neg-d)) >=>
                         minus-double-inverse)) >=>
        sym *-assoc

opaque
  unfolding ℚ

  ℚ->split-ℤ : (q : ℚ) -> ∃[ n ∈ ℤ ] Σ[ d ∈ ℤ ] (NonZero d × (ℤ->ℚ n == q * ℤ->ℚ d))
  ℚ->split-ℤ =
    SetQuotientElim.elimProp (\_ -> squash) (\q' -> ∣ handle (ℚ'->split-ℤ q') ∣)
    where
    handle : {q' : ℚ'} ->
        (Σ[ n ∈ ℤ ] Σ[ d ∈ ℤ ] (NonZero d × (ℤ->ℚ' n r~ (q' r*' ℤ->ℚ' d)))) ->
        (Σ[ n ∈ ℤ ] Σ[ d ∈ ℤ ] (NonZero d × (ℤ->ℚ n == ℚ'->ℚ q' * ℤ->ℚ d)))
    handle (n , d , (nz-d , p)) = n , d , (nz-d , (r~->path _ _ p) >=> (sym r*-eval))

  ℚ->split-ℤℕ⁺ : (q : ℚ) -> ∃[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (ℤ->ℚ n == q * ℕ->ℚ ⟨ d ⟩)
  ℚ->split-ℤℕ⁺ =
    SetQuotientElim.elimProp (\_ -> squash) (\q' -> ∣ handle (ℚ'->split-ℤℕ⁺ q') ∣)
    where
    handle : {q' : ℚ'} ->
        (Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (ℤ->ℚ' n r~ (q' r*' ℕ->ℚ' ⟨ d ⟩))) ->
        (Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (ℤ->ℚ n == ℚ'->ℚ q' * ℕ->ℚ ⟨ d ⟩))
    handle (n , d , p) = n , d , (r~->path _ _ p) >=> (sym r*-eval)




opaque
  unfolding ℚ
  private
    isNonZeroℚ' : ℚ -> hProp ℓ-zero
    isNonZeroℚ' =
      SetQuotientElim.elim (\_ -> isSet-hProp) val preserved
      where
      val : ℚ' -> hProp ℓ-zero
      val r = NonZero (numer r) , int.isPropNonZero
      preserved : (a b : ℚ') -> (a r~ b) -> val a == val b
      preserved a b path = ΣProp-path isProp-isProp (ua (isoToEquiv i))
        where
        open Iso
        open int
        i : Iso (⟨ val a ⟩) (⟨ val b ⟩)
        i .fun nz = *-NonZero₁ (subst NonZero path (*-NonZero-NonZero nz (rNonZero b)))
        i .inv nz = *-NonZero₁ (subst NonZero (sym path) (*-NonZero-NonZero nz (rNonZero a)))
        i .rightInv _ = int.isPropNonZero _ _
        i .leftInv _ = int.isPropNonZero _ _

  isNonZeroℚ : ℚ -> Type₀
  isNonZeroℚ r = fst (isNonZeroℚ' r)
  isProp-isNonZeroℚ : (r : ℚ) -> isProp (isNonZeroℚ r)
  isProp-isNonZeroℚ r = snd (isNonZeroℚ' r)

opaque
  unfolding isNonZeroℚ

  ¬isNonZeroℚ-0r : ¬ (isNonZeroℚ 0r)
  ¬isNonZeroℚ-0r b = int.NonZero->¬Zero b tt

  isNonZeroℚ-1r : (isNonZeroℚ 1r)
  isNonZeroℚ-1r = inj-l tt

1r!=0r : 1r != 0r
1r!=0r 1r=0r = ¬isNonZeroℚ-0r (subst isNonZeroℚ 1r=0r isNonZeroℚ-1r)

isNonZeroℚ->ℚInv : {r : ℚ} -> isNonZeroℚ r -> ℚInv r
isNonZeroℚ->ℚInv nz p = ¬isNonZeroℚ-0r (subst isNonZeroℚ p nz)

opaque
  unfolding isNonZeroℚ

  Pos'->NonZeroℚ : {n : Nat} -> Pos' n -> isNonZeroℚ (ℕ->ℚ n)
  Pos'->NonZeroℚ {n = (suc _)} _ = inj-l tt

opaque
  unfolding isNonZeroℚ _r*_

  r*-isNonZeroℚ-isNonZeroℚ : (a b : ℚ) -> isNonZeroℚ a -> isNonZeroℚ b -> isNonZeroℚ (a r* b)
  r*-isNonZeroℚ-isNonZeroℚ =
    SetQuotientElim.elimProp2 {C2 = \a b -> isNonZeroℚ a -> isNonZeroℚ b -> isNonZeroℚ (a r* b)}
      (\a b -> isPropΠ2 (\_ _ -> isProp-isNonZeroℚ (a r* b)))
      (\a b nza nzb -> int.*-NonZero-NonZero nza nzb)

opaque
  unfolding isNonZeroℚ r1/

  r1/-isNonZeroℚ : (a : ℚ) -> (nz : isNonZeroℚ a) -> isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz))
  r1/-isNonZeroℚ =
    SetQuotientElim.elimProp {C = \a -> (nz : isNonZeroℚ a) -> isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz))}
      (\a -> isPropΠ (\ nz -> (isProp-isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz)))))
      (\a nz -> rNonZero a)

NonZeroℚ : Type₀
NonZeroℚ = Σ ℚ isNonZeroℚ

_r^ℕ_ : NonZeroℚ -> ℕ -> NonZeroℚ
a r^ℕ zero = 1r , isNonZeroℚ-1r
a r^ℕ (suc n) = (fst a) r* (fst rec) , r*-isNonZeroℚ-isNonZeroℚ (fst a) (fst rec) (snd a) (snd rec)
  where
  rec = (a r^ℕ n)

_r^ℤ_ : NonZeroℚ -> ℤ -> NonZeroℚ
a r^ℤ (nonneg n) = a r^ℕ n
a r^ℤ (neg n) = r1/ (fst rec) (isNonZeroℚ->ℚInv (snd rec)) , r1/-isNonZeroℚ (fst rec) (snd rec)
  where
  rec = (a r^ℕ (suc n))

-- Standard rationals


1/ℕ' : Nat⁺ -> ℚ'
1/ℕ' (n , pos-n) = record
  { numerator = (ℕ->ℤ 1)
  ; denominator = (ℕ->ℤ n)
  ; NonZero-denominator = Posℕ->NonZeroℤ n pos-n
  }
  where
  Posℕ->NonZeroℤ : (n : Nat) -> (Pos' n) -> (int.NonZero (ℕ->ℤ n))
  Posℕ->NonZeroℤ (suc _) _ = (inj-l tt)

1/ℕ : Nat⁺ -> ℚ
1/ℕ n = ℚ'->ℚ (1/ℕ' n)

1/2r : ℚ
1/2r = 1/ℕ 2⁺

1/2r' : ℚ'
1/2r' = 1/ℕ' 2⁺

2r' : ℚ'
2r' = record
  { numerator = (ℕ->ℤ 2)
  ; denominator = (ℕ->ℤ 1)
  ; NonZero-denominator = (inj-l tt)
  }

2r : ℚ
2r = ℚ'->ℚ 2r'

opaque
  unfolding _r+_

  2r-path-base : 1r r+ 1r == 2r
  2r-path-base = cong [_] (nd-paths->path _ _ n-path d-path)
    where
    2z-path : (int 1) + (int 1) == (int 2)
    2z-path = int.add1-extract-right >=> sym int.add1-extract-left >=> +-right-zero

    n-path : numer (1r' r+' 1r') == numer 2r'
    n-path = cong numer (r+'-eval {1r'} {1r'}) >=> (cong2 _+_ *-left-one *-left-one) >=> 2z-path
    d-path : denom (1r' r+' 1r') == denom 2r'
    d-path = cong denom (r+'-eval {1r'} {1r'}) >=> *-left-one

  2r-path : (q : ℚ) -> q r+ q == 2r r* q
  2r-path q =
    cong2 _r+_ (sym (r*-left-one q)) (sym (r*-left-one q)) >=>
    sym (r*-distrib-r+-right 1r 1r q) >=>
    cong (_r* q) 2r-path-base

opaque
  unfolding _r*_

  2r-1/2r-path : 2r r* 1/2r == 1r
  2r-1/2r-path = eq/ (2r' r*' 1/2r') 1r' path
    where
    path : (((int 2) * (int 1)) * (int 1)) == (int 1) * ((int 1) * (int 2))
    path = *-commute >=> cong ((int 1) *_) *-commute

opaque
  unfolding _r*_ _r+_

  1/2r-path : (q : ℚ) -> (q r* 1/2r) r+ (q r* 1/2r) == q
  1/2r-path q = 2r-path (q r* 1/2r) >=> r*-commute 2r (q r* 1/2r) >=>
                r*-assoc q 1/2r 2r >=> cong (q r*_) (r*-commute 1/2r 2r >=> 2r-1/2r-path) >=>
                r*-right-one q

  1/2r-path' : (q : ℚ) -> (1/2r r* q) r+ (1/2r r* q) == q
  1/2r-path' q = cong2 _r+_ (r*-commute 1/2r q) (r*-commute 1/2r q) >=> 1/2r-path q

  1/2r-1/2r-path : 1/2r + 1/2r == 1r
  1/2r-1/2r-path = +-cong (sym (*-left-oneᵉ 1/2r)) (sym (*-left-oneᵉ 1/2r)) >=> 1/2r-path 1r

  1/2ℕ'-r~ : (n : Nat⁺) -> (1/ℕ' (2⁺ *⁺ n)) r~ (1/2r' r*' 1/ℕ' n)
  1/2ℕ'-r~ n =
    *-left-one >=> sym int-inject-*' >=>
    sym *-left-one >=> *-left (sym *-left-one)

  1/2ℕ-path : (n : Nat⁺) -> (1/ℕ (2⁺ *⁺ n)) == (1/2r r* 1/ℕ n)
  1/2ℕ-path n = eq/ _ _ (1/2ℕ'-r~ n)

  1/ℕ-ℕ-r~ : (n : Nat⁺) -> ((1/ℕ' n) r*' (ℕ->ℚ' ⟨ n ⟩)) r~ 1r'
  1/ℕ-ℕ-r~ n =
    *-right-one >=> *-left-one >=> sym *-right-one >=> sym *-left-one

  1/ℕ-ℕ-path : (n : Nat⁺) -> (1/ℕ n) r* (ℕ->ℚ ⟨ n ⟩) == 1r
  1/ℕ-ℕ-path n = eq/ _ _ (1/ℕ-ℕ-r~ n)

  1/2^ℕ-path : (n : Nat) -> 1/ℕ (2⁺ ^⁺ n) == 1/2r ^ℕ n
  1/2^ℕ-path zero = refl
  1/2^ℕ-path (suc n) = 1/2ℕ-path (2⁺ ^⁺ n) >=> cong (1/2r r*_) (1/2^ℕ-path n)

  1/ℕ-distrib-* : (m n : Nat⁺) -> 1/ℕ (m *⁺ n) == 1/ℕ m * 1/ℕ n
  1/ℕ-distrib-* m n = eq/ _ _ 1/ℕ'-distrib-*-r~
    where
    1/ℕ'-distrib-*-r~ : (1/ℕ' (m *⁺ n)) r~ (1/ℕ' m r*' 1/ℕ' n)
    1/ℕ'-distrib-*-r~ =
      *-cong (sym *-left-one) (sym (Semiringʰ.preserves-* Semiringʰ-ℕ->ℤ ⟨ m ⟩ ⟨ n ⟩))

opaque
  ℚ->split-ℤ/ℕ : (q : ℚ) -> ∃[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d)
  ℚ->split-ℤ/ℕ q = ∥-map handle (ℚ->split-ℤℕ⁺ q)
    where
    handle :
        Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (ℤ->ℚ n == q * ℕ->ℚ ⟨ d ⟩) ->
        Σ[ n ∈ ℤ ] Σ[ d ∈ Nat⁺ ] (q == ℤ->ℚ n * 1/ℕ d)
    handle (n , d , p) = n , d , p'
      where
      module _ where
        p' : (q == ℤ->ℚ n * 1/ℕ d)
        p' = sym (cong (_* 1/ℕ d) p >=>
                  *-assoc >=>
                  *-right (*-commute >=> 1/ℕ-ℕ-path d) >=>
                  *-right-one)
