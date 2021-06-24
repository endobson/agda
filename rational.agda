{-# OPTIONS --cubical --safe --exact-split #-}

module rational where

open import abs
open import base
open import cubical using (_∧_ ; _∨_ ; ~_)
open import equality
open import equivalence
open import fin
open import functions
open import funext
open import nat
open import hlevel
open import quotient-remainder-int
open import relation
open import set-quotient
open import univalence
open import isomorphism
open import sigma
import int
import solver

open int using (int ; Int ; NonZero ; ℕ->ℤ ; ℤ ; nonneg ; neg)
open solver using (_⊗_ ; _⊕_)

record Rational' : Type₀ where
  field
    numerator : Int
    denominator : Int
    NonZero-denominator : NonZero denominator


private
  numer : Rational' -> Int
  numer = Rational'.numerator
  denom : Rational' -> Int
  denom = Rational'.denominator
  rNonZero : (r : Rational') -> NonZero (denom r)
  rNonZero = Rational'.NonZero-denominator


-- Discrete-Rational' : Discrete Rational'
-- Discrete-Rational' = ?
--
-- isSet-Rational' : isSet Rational'
-- isSet-Rational' = Discrete->isSet Discrete-Rational'


private

  _i*_ = int._*_
  _i+_ = int._+_
  i-_ = int.-_

_r~_ : Rel Rational' ℓ-zero
_r~_ a b = (numer a) i* (denom b) == (numer b) i* (denom a)

record _r~'_ (a : Rational') (b : Rational') : Type₀ where
  field
    path : a r~ b

r~'->r~ : {a b : Rational'} -> a r~' b -> a r~ b
r~'->r~ v = _r~'_.path v

r~->r~' : {a b : Rational'} -> a r~ b -> a r~' b
r~->r~' {a} {b} v = record { path = v }

Rational : Type₀
Rational = Rational' / _r~_

ℚ = Rational

trans-r~ : (a b c : Rational') -> a r~ b -> b r~ c -> a r~ c
trans-r~ a b c p1 p2 = int.*-right-injective (rNonZero b) p3
  where
  na = numer a
  nb = numer b
  nc = numer c
  da = denom a
  db = denom b
  dc = denom c

  p3 : (na i* dc) i* db == (nc i* da) i* db
  p3 = int.*-left int.*-commute >=> int.*-assoc >=> cong (dc i*_) p1 >=>
       sym int.*-assoc >=> int.*-left (int.*-commute >=> p2) >=>
       int.*-assoc >=> int.*-right int.*-commute >=> sym int.*-assoc

refl-r~ : {a : Rational'} -> a r~ a
refl-r~ = refl

path->r~ : {a b : Rational'} -> a == b -> a r~ b
path->r~ {a} p = subst (a r~_) p (refl-r~ {a})


trans-r~' : {a b c : Rational'} -> a r~' b -> b r~' c -> a r~' c
trans-r~' {a} {b} {c} p1 p2 = r~->r~' (trans-r~ a b c (r~'->r~ p1) (r~'->r~ p2))

nd-paths->path : (a b : Rational') -> (numer a == numer b) -> (denom a == denom b) -> a == b
nd-paths->path a b pn pd = (\i -> record
  { numerator = pn i
  ; denominator = pd i
  ; NonZero-denominator = pnz i
  })
  where
  pnz : PathP (\i -> NonZero (pd i)) (rNonZero a) (rNonZero b)
  pnz = isProp->PathP (\_ -> int.isPropNonZero) _ _

_r+'ᵉ_ : Rational' -> Rational' -> Rational'
a r+'ᵉ b = record
  { numerator = ((numer a) i* (denom b)) i+ ((numer b) i* (denom a))
  ; denominator = (denom a) i* (denom b)
  ; NonZero-denominator = int.*-NonZero-NonZero (rNonZero a) (rNonZero b)
  }

abstract
  _r+'_ : Rational' -> Rational' -> Rational'
  a r+' b = a r+'ᵉ b

  r+'-eval : {a b : Rational'} -> a r+' b == a r+'ᵉ b
  r+'-eval = refl

  r+'-commute : (a b : Rational') -> a r+' b == b r+' a
  r+'-commute a b = nd-paths->path ab ba n-p d-p
    where
    ab = a r+' b
    ba = b r+' a
    na = numer a
    nb = numer b
    da = denom a
    db = denom b

    n-p : numer ab == numer ba
    n-p = int.+-commute {na i* db} {nb i* da}

    d-p : denom ab == denom ba
    d-p = int.*-commute {da} {db}


  r+'-preserves-r~₂ : (a b1 b2 : Rational') -> b1 r~ b2 -> (a r+' b1) r~ (a r+' b2)
  r+'-preserves-r~₂ a b1 b2 r = path
    where
    path'1 : (nx dx ny dy nz dz : Int) ->
      (((nx i* dy) i+ (ny i* dx)) i* (dx i* dz))
      ==
      ((nx i* dx) i* (dy i* dz)) i+ ((dx i* dx) i* (ny i* dz))
    path'1 =
      solver.IntSolver.solve 6
      (\ nx dx ny dy nz dz ->
         ((((nx ⊗ dy) ⊕ (ny ⊗ dx)) ⊗ (dx ⊗ dz)) ,
          ((nx ⊗ dx) ⊗ (dy ⊗ dz)) ⊕ ((dx ⊗ dx) ⊗ (ny ⊗ dz))))
      refl

    path'2 : (nx dx ny dy nz dz : Int) ->
      (((nx i* dz) i+ (nz i* dx)) i* (dx i* dy))
      ==
      ((nx i* dx) i* (dy i* dz)) i+ ((dx i* dx) i* (nz i* dy))
    path'2 =
      solver.IntSolver.solve 6
      (\ nx dx ny dy nz dz ->
         ((((nx ⊗ dz) ⊕ (nz ⊗ dx)) ⊗ (dx ⊗ dy)) ,
          ((nx ⊗ dx) ⊗ (dy ⊗ dz)) ⊕ ((dx ⊗ dx) ⊗ (nz ⊗ dy))))
      refl

    path :
      ((((numer a) i* (denom b1)) i+ ((numer b1) i* (denom a))) i* ((denom a) i*
      (denom b2)))
      ==
      ((((numer a) i* (denom b2)) i+ ((numer b2) i* (denom a))) i*
       ((denom a) i* (denom b1)))
    path =
      path'1 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2)
      >=> cong ((((numer a) i* (denom a)) i* ((denom b1) i* (denom b2))) i+_)
               (cong (((denom a) i* (denom a)) i*_) r)
      >=> sym (path'2 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))

  r+'-preserves-r~₁ : (b a1 a2 : Rational') -> a1 r~ a2 -> (a1 r+' b) r~ (a2 r+' b)
  r+'-preserves-r~₁ b a1 a2 r =
    transport (\i -> (r+'-commute b a1 i) r~ (r+'-commute b a2 i)) (r+'-preserves-r~₂ b a1 a2 r)


same-denom-r+' : (a b : Rational') -> Rational'
same-denom-r+' a b = record
  { numerator = numer a int.+ numer b
  ; denominator = denom a
  ; NonZero-denominator = rNonZero a
  }

abstract
  same-denom-r+'-r~ : (a b : Rational') -> denom a == denom b -> same-denom-r+' a b r~ (a r+' b)
  same-denom-r+'-r~ a b p =
   int.*-distrib-+ >=>
   cong2 int._+_ (int.*-right int.*-commute >=> sym int.*-assoc)
                 (int.*-right (int.*-right (sym p)) >=> sym int.*-assoc) >=>
   sym int.*-distrib-+

module RationalElim = SetQuotientElim Rational' _r~_

_r+ᵉ_ : Rational -> Rational -> Rational
_r+ᵉ_ = RationalElim.rec2 squash/
          (\a b -> [ a r+' b ])
          (\b a1 a2 r -> eq/ _ _ (r+'-preserves-r~₁ b a1 a2 r))
          (\a b1 b2 r -> eq/ _ _ (r+'-preserves-r~₂ a b1 b2 r))


abstract
  _r+_ : Rational -> Rational -> Rational
  _r+_ = _r+ᵉ_

  r+-eval : {a b : Rational} -> a r+ b == a r+ᵉ b
  r+-eval = refl

isSetRational : isSet Rational
isSetRational = squash/

abstract
  r+-commute : (a b : Rational) -> (a r+ b) == (b r+ a)
  r+-commute = RationalElim.elimProp2 (\a b -> isSetRational _ _) (\a b -> cong [_] (r+'-commute a b))

0r' : Rational'
0r' = record
  { numerator = (int 0)
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

abstract
  r+'-left-zero : (a : Rational') -> (0r' r+' a) == a
  r+'-left-zero a = nd-paths->path 0a a pn pd
    where
    na = numer a
    da = denom a
    0a = (0r' r+' a)


    pn' : ((int 0) i* (denom a)) i+ ((numer a) i* (int 1)) == (numer a)
    pn' = cong (_i+ ((numer a) i* (int 1))) (int.*-left-zero {denom a})
          >=> int.+-left-zero
          >=> int.*-right-one

    pn : (numer 0a) == (numer a)
    pn = pn'

    pd : (denom 0a) == (denom a)
    pd = int.*-left-one

0r : Rational
0r = [ 0r' ]

abstract
  r+-left-zero : (a : Rational) -> (0r r+ a) == a
  r+-left-zero = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> cong [_] (r+'-left-zero a))

  r+-right-zero : (a : Rational) -> (a r+ 0r) == a
  r+-right-zero a = r+-commute a 0r >=> r+-left-zero a

_r*'_ : Rational' -> Rational' -> Rational'
a r*' b = record
  { numerator = (numer a) i* (numer b)
  ; denominator = (denom a) i* (denom b)
  ; NonZero-denominator = int.*-NonZero-NonZero (rNonZero a) (rNonZero b)
  }

r*'-commute : (a b : Rational') -> a r*' b == b r*' a
r*'-commute a b = nd-paths->path ab ba n-p d-p
  where
  ab = a r*' b
  ba = b r*' a
  na = numer a
  nb = numer b
  da = denom a
  db = denom b

  n-p : numer ab == numer ba
  n-p = int.*-commute {na} {nb}

  d-p : denom ab == denom ba
  d-p = int.*-commute {da} {db}


r*'-preserves-r~₂ : (a b1 b2 : Rational') -> b1 r~ b2 -> (a r*' b1) r~ (a r*' b2)
r*'-preserves-r~₂ a b1 b2 r = path
  where
  ab1 = a r*' b1
  ab2 = a r*' b2

  path1 : (nx dx ny dy nz dz : Int) ->
    (nx i* ny) i* (dx i* dz) == (nx i* dx) i* (ny i* dz)
  path1 = solver.IntSolver.solve 6
          (\ nx dx ny dy nz dz  ->
             (nx ⊗ ny) ⊗ (dx ⊗ dz) , (nx ⊗ dx) ⊗ (ny ⊗ dz)) refl

  path2 : (nx dx ny dy nz dz : Int) ->
    (nx i* nz) i* (dx i* dy) == (nx i* dx) i* (nz i* dy)
  path2 = solver.IntSolver.solve 6
          (\ nx dx ny dy nz dz  ->
             (nx ⊗ nz) ⊗ (dx ⊗ dy) , (nx ⊗ dx) ⊗ (nz ⊗ dy)) refl

  path : (numer ab1) i* (denom ab2) == (numer ab2) i* (denom ab1)
  path = (path1 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))
         >=> cong (((numer a) i* (denom a)) i*_) r
         >=> sym (path2 (numer a) (denom a) (numer b1) (denom b1) (numer b2) (denom b2))

r*'-preserves-r~₁ : (b a1 a2 : Rational') -> a1 r~ a2 -> (a1 r*' b) r~ (a2 r*' b)
r*'-preserves-r~₁ b a1 a2 r =
  transport (\i -> (r*'-commute b a1 i) r~ (r*'-commute b a2 i)) (r*'-preserves-r~₂ b a1 a2 r)

_r*ᵉ_ : Rational -> Rational -> Rational
_r*ᵉ_ = RationalElim.rec2 squash/
          (\a b -> [ a r*' b ])
          (\b a1 a2 r -> eq/ _ _ (r*'-preserves-r~₁ b a1 a2 r))
          (\a b1 b2 r -> eq/ _ _ (r*'-preserves-r~₂ a b1 b2 r))

abstract
  _r*_ : Rational -> Rational -> Rational
  _r*_ = _r*ᵉ_

  r*-eval : {a b : Rational} -> a r* b == a r*ᵉ b
  r*-eval = refl

  r*-commute : (a b : Rational) -> (a r* b) == (b r* a)
  r*-commute = RationalElim.elimProp2 (\a b -> isSetRational _ _) (\a b -> cong [_] (r*'-commute a b))

  r*'-left-zero : (a : Rational') -> (0r' r*' a) r~ 0r'
  r*'-left-zero a = int.*-right-one {numer (0r' r*' a)}
                    >=> int.*-left-zero {numer a}
                    >=> sym (int.*-left-zero {denom (0r' r*' a)})

  r*-left-zero : (a : Rational) -> (0r r* a) == 0r
  r*-left-zero = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> eq/ _ _ (r*'-left-zero a))

  r*-right-zero : (a : Rational) -> (a r* 0r) == 0r
  r*-right-zero a = r*-commute a 0r >=> r*-left-zero a

1r' : Rational'
1r' = record
  { numerator = (int 1)
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

1r : Rational
1r = [ 1r' ]

r*'-left-one : (a : Rational') -> (1r' r*' a) == a
r*'-left-one a = nd-paths->path _ _ (int.*-left-one {numer a}) (int.*-left-one {denom a})

abstract
  r*-left-one : (a : Rational) -> (1r r* a) == a
  r*-left-one = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> cong [_] (r*'-left-one a))

  r*-right-one : (a : Rational) -> (a r* 1r) == a
  r*-right-one a = r*-commute a 1r >=> r*-left-one a

r*'-assoc : (a b c : Rational') -> ((a r*' b) r*' c) == (a r*' (b r*' c))
r*'-assoc a b c = nd-paths->path _ _ (int.*-assoc {numer a} {numer b} {numer c})
                                     (int.*-assoc {denom a} {denom b} {denom c})

abstract
  r*-assoc : (a b c : Rational) -> ((a r* b) r* c) == (a r* (b r* c))
  r*-assoc = RationalElim.elimProp3 (\a b c -> isSetRational _ _) (\a b c -> cong [_] (r*'-assoc a b c))

abstract
  r+'-assoc : {a b c : Rational'} -> ((a r+' b) r+' c) r~ (a r+' (b r+' c))
  r+'-assoc {a} {b} {c} = path
    where
    na = numer a
    nb = numer b
    nc = numer c
    da = denom a
    db = denom b
    dc = denom c

    path : ((((na i* db) i+ (nb i* da)) i* dc) i+ (nc i* (da i* db)))
           i* (da i* (db i* dc))
           ==
           ((na i* (db i* dc)) i+ (((nb i* dc) i+ (nc i* db)) i* da))
           i* ((da i* db) i* dc)
    path = solver.IntSolver.solve 6
           (\ na da nb db nc dc ->
              ((((na ⊗ db) ⊕ (nb ⊗ da)) ⊗ dc) ⊕ (nc ⊗ (da ⊗ db))) ⊗ (da ⊗ (db ⊗ dc)) ,
              ((na ⊗ (db ⊗ dc)) ⊕ (((nb ⊗ dc) ⊕ (nc ⊗ db)) ⊗ da)) ⊗ ((da ⊗ db) ⊗ dc))
           refl na da nb db nc dc

r+'-assoc' : {a b c : Rational'} -> ((a r+' b) r+' c) r~' (a r+' (b r+' c))
r+'-assoc' = r~->r~' r+'-assoc

abstract
  r+-assoc : (a b c : Rational) -> ((a r+ b) r+ c) == (a r+ (b r+ c))
  r+-assoc = RationalElim.elimProp3
               (\a b c -> isSetRational ((a r+ b) r+ c) (a r+ (b r+ c)))
               (\a b c -> (eq/ ((a r+' b) r+' c) (a r+' (b r+' c)) (r+'-assoc {a} {b} {c})))

abstract
  r*'-distrib-r+'-right : (a b c : Rational') -> ((a r+' b) r*' c) r~ ((a r*' c) r+' (b r*' c))
  r*'-distrib-r+'-right a b c = path
    where
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

    path : (((na i* db) i+ (nb i* da)) i* nc) i* ((da i* dc) i* (db i* dc))
           == (((na i* nc) i* (db i* dc)) i+ ((nb i* nc) i* (da i* dc))) i* ((da i* db) i* dc)
    path = solver.IntSolver.solve 6
           (\ na da nb db nc dc ->
              (((na ⊗ db) ⊕ (nb ⊗ da)) ⊗ nc) ⊗ ((da ⊗ dc) ⊗ (db ⊗ dc)) ,
              (((na ⊗ nc) ⊗ (db ⊗ dc)) ⊕ ((nb ⊗ nc) ⊗ (da ⊗ dc))) ⊗ ((da ⊗ db) ⊗ dc))
           refl na da nb db nc dc

abstract
  r*-distrib-r+-right : (a b c : Rational) -> ((a r+ b) r* c) == ((a r* c) r+ (b r* c))
  r*-distrib-r+-right =
    RationalElim.elimProp3 (\a b c -> isSetRational _ _) (\a b c -> (eq/ _ _ (r*'-distrib-r+'-right a b c)))

r-' : Rational' -> Rational'
r-' a = record
  { numerator = i- (Rational'.numerator a)
  ; denominator = Rational'.denominator a
  ; NonZero-denominator = Rational'.NonZero-denominator a
  }

r-'-preserves-r~ : (a1 a2 : Rational') -> a1 r~ a2 -> (r-' a1) r~ (r-' a2)
r-'-preserves-r~ a1 a2 r =
  int.minus-extract-left {na1} {da2} >=> cong i-_ r >=> sym (int.minus-extract-left {na2} {da1})
  where
  na1 = numer a1
  da1 = denom a1
  na2 = numer a2
  da2 = denom a2

abstract
  r+'-inverse : (a : Rational') -> (a r+' (r-' a)) r~ 0r'
  r+'-inverse a =
    int.*-right-one {(na i* da) i+ ((i- na) i* da)}
    >=> sym (int.*-distrib-+ {na} {i- na} {da})
    >=> cong (_i* da) (int.add-minus-zero {na})
    >=> int.*-left-zero {da}
    >=> sym (int.*-left-zero {denom a i* denom a})
    where
    na = numer a
    da = denom a


r-_ : Rational -> Rational
r-_ = RationalElim.rec isSetRational (\a -> [ r-' a ]) (\a1 a2 r -> eq/ _ _ (r-'-preserves-r~ a1 a2 r))

abstract
  r+-inverse : (a : Rational) -> (a r+ (r- a)) == 0r
  r+-inverse = RationalElim.elimProp
               (\_ -> isSetRational _ _)
               (\a -> eq/ _ _ (r+'-inverse a))

  r*-minus-extract-left : (a1 a2 : Rational) -> (r- a1) r* a2 == r- (a1 r* a2)
  r*-minus-extract-left =
    RationalElim.elimProp2
      (\_ _ -> isSetRational _ _)
      (\a1 a2 -> cong [_] (nd-paths->path _ _ int.minus-extract-left refl))

  r*-minus-extract-right : (a1 a2 : Rational) -> a1 r* (r- a2) == r- (a1 r* a2)
  r*-minus-extract-right a1 a2 = r*-commute a1 (r- a2) >=> r*-minus-extract-left a2 a1 >=>
                                 cong r-_ (r*-commute a2 a1)

ℚInv' : Pred Rational' ℓ-zero
ℚInv' a = NonZero (numer a)

isProp-ℚInv' : {a : Rational'} -> isProp (ℚInv' a)
isProp-ℚInv' = int.isPropNonZero

r1/' : (a : Rational') -> ℚInv' a -> Rational'
r1/' a i = record
  { numerator = Rational'.denominator a
  ; denominator = Rational'.numerator a
  ; NonZero-denominator = i
  }

r1/'-preserves-r~ : (a1 a2 : Rational') -> (i1 : ℚInv' a1) -> (i2 : ℚInv' a2) -> a1 r~ a2 ->
                    (r1/' a1 i1) r~ (r1/' a2 i2)
r1/'-preserves-r~ a1 a2 _ _ r =
  int.*-commute {denom a1} {numer a2} >=> sym r >=> int.*-commute {numer a1} {denom a2}


r1/'-inverse : (a : Rational') -> (i : ℚInv' a) -> ((r1/' a i) r*' a) r~ 1r'
r1/'-inverse a i = path
  where
  path : ((denom a) i* (numer a)) i* (int 1) == (int 1) i* ((numer a) i* (denom a))
  path = int.*-right-one {(denom a) i* (numer a)} >=> int.*-commute {denom a} {numer a}
         >=> sym int.*-left-one

ℚInv : Pred Rational ℓ-zero
ℚInv a = (a != 0r)


ℚInv->ℚInv' : (a : Rational') -> ℚInv ([ a ]) -> ℚInv' a
ℚInv->ℚInv' a i = handle (numer a) refl
  where
  handle : (x : Int) -> (x == numer a) -> ℚInv' a
  handle (int.nonneg (suc _)) p = subst NonZero p (inj-l tt)
  handle (int.neg _) p = subst NonZero p (inj-r tt)
  handle (int.nonneg zero) p = bot-elim (i (eq/ a 0r' path))
    where
    path : a r~ 0r'
    path = int.*-right-one {numer a} >=> sym p >=> sym int.*-left-zero

module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A -> Type ℓb} {C : Type ℓc}
         (a1 a2 : A)
         {f1 : (B a1) -> C}
         {f2 : (B a2) -> C}
         {p : (B a1) == (B a2)}
         (same : (b1 : (B a1)) (b2 : (B a2)) -> (f1 b1) == (f2 b2))
         where
  private
    f-path-t : PathP (\k -> (p k) -> C)
                     (\x -> f1 (transport refl x))
                     (\x -> f2 (transport refl x))
    f-path-t k x = same x1 x2 k
      where
      x1 : B a1
      x1 = transport (\j -> p (~ j ∧ k)) x
      x2 : B a2
      x2 = transport (\j -> p (j ∨ k)) x

    f-path-left : f1 ∘ (transport refl) == f1
    f-path-left = funExt (\x -> cong f1 (transportRefl x))

    f-path-right : f2 ∘ (transport refl) == f2
    f-path-right = funExt (\x -> cong f2 (transportRefl x))

  funExtDep : PathP (\k -> (p k) -> C) f1 f2
  funExtDep = transP-left (transP-right (sym f-path-left) f-path-t) f-path-right


r1/ : (a : Rational) -> (ℚInv a) -> Rational
r1/ = RationalElim.elim
        (\_ -> isSetΠ (\_ -> isSetRational))
        g
        g'
  where
  g : (a : Rational') -> ℚInv ([ a ]) -> Rational
  g a i = [ r1/' a (ℚInv->ℚInv' a i) ]

  g' : (a1 a2 : Rational') -> (r : (a1 r~ a2)) ->
       PathP (\k -> (ℚInv (eq/ a1 a2 r k)) -> Rational) (g a1) (g a2)
  g' a1 a2 r = funExtDep a1 a2 same
    where
    same : (i1 : (ℚInv [ a1 ])) -> (i2 : (ℚInv [ a2 ])) -> (g a1 i1) == (g a2 i2)
    same i1 i2 = eq/ (r1/' a1 (ℚInv->ℚInv' a1 i1)) (r1/' a2 (ℚInv->ℚInv' a2 i2))
                     (r1/'-preserves-r~ a1 a2 (ℚInv->ℚInv' a1 i1) (ℚInv->ℚInv' a2 i2) r)

abstract
  r1/-inverse : (a : Rational) -> (i : ℚInv a) -> ((r1/ a i) r* a) == 1r
  r1/-inverse = RationalElim.elimProp
                 (\_ -> isPropΠ (\_ -> isSetRational _ _))
                 (\ a i -> eq/ _ _ (r1/'-inverse a (ℚInv->ℚInv' _ i)))


ℤ->ℚ' : Int -> Rational'
ℤ->ℚ' x = record
  { numerator = x
  ; denominator = (int 1)
  ; NonZero-denominator = (inj-l tt)
  }

ℤ->ℚ : Int -> Rational
ℤ->ℚ x = [ ℤ->ℚ' x ]

ℕ->ℚ' : Nat -> Rational'
ℕ->ℚ' n = ℤ->ℚ' (ℕ->ℤ n)

ℕ->ℚ : Nat -> Rational
ℕ->ℚ n = ℤ->ℚ (ℕ->ℤ n)

abstract
  ℤ->ℚ-preserves-+ : (x y : Int) -> ℤ->ℚ (x i+ y) == ℤ->ℚ x r+ ℤ->ℚ y
  ℤ->ℚ-preserves-+ x y = eq/ _ _ r
    where
    r1 : (x i+ y) i* ((int 1) i* (int 1)) == (x i+ y)
    r1 = cong ((x i+ y) i*_) int.*-right-one >=> int.*-right-one {x i+ y}

    r2 : ((x i* (int 1)) i+ (y i* (int 1))) i* (int 1) == (x i+ y)
    r2 = int.*-right-one {(x i* (int 1)) i+ (y i* (int 1))}
         >=> cong2 _i+_ (int.*-right-one {x}) (int.*-right-one {y})

    r : (x i+ y) i* ((int 1) i* (int 1)) == ((x i* (int 1)) i+ (y i* (int 1))) i* (int 1)
    r = r1 >=> sym r2

  ℤ->ℚ-preserves-* : (x y : Int) -> ℤ->ℚ (x i* y) == ℤ->ℚ x r* ℤ->ℚ y
  ℤ->ℚ-preserves-* x y = cong [_] (nd-paths->path _ _ refl (sym int.*-left-one))


ℤ->ℚ-preserves-minus : (x : Int) -> ℤ->ℚ (int.- x) == r- (ℤ->ℚ x)
ℤ->ℚ-preserves-minus x = cong [_] refl

private
  isNonZeroℚ' : ℚ -> hProp ℓ-zero
  isNonZeroℚ' =
    RationalElim.elim (\_ -> isSet-hProp) val preserved
    where
    val : Rational' -> hProp ℓ-zero
    val r = NonZero (numer r) , int.isPropNonZero
    preserved : (a b : Rational') -> (a r~ b) -> val a == val b
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

¬isNonZeroℚ-0r : ¬ (isNonZeroℚ 0r)
¬isNonZeroℚ-0r b = int.NonZero->¬Zero b tt

isNonZeroℚ-1r : (isNonZeroℚ 1r)
isNonZeroℚ-1r = inj-l tt

isNonZeroℚ->ℚInv : {r : ℚ} -> isNonZeroℚ r -> ℚInv r
isNonZeroℚ->ℚInv nz p = ¬isNonZeroℚ-0r (subst isNonZeroℚ p nz)

Pos'->NonZeroℚ : {n : Nat} -> Pos' n -> isNonZeroℚ (ℕ->ℚ n)
Pos'->NonZeroℚ {n = (suc _)} _ = inj-l tt

abstract
  r*-isNonZeroℚ-isNonZeroℚ : (a b : ℚ) -> isNonZeroℚ a -> isNonZeroℚ b -> isNonZeroℚ (a r* b)
  r*-isNonZeroℚ-isNonZeroℚ =
    RationalElim.elimProp2 {C2 = \a b -> isNonZeroℚ a -> isNonZeroℚ b -> isNonZeroℚ (a r* b)}
      (\a b -> isPropΠ2 (\_ _ -> isProp-isNonZeroℚ (a r* b)))
      (\a b nza nzb -> int.*-NonZero-NonZero nza nzb)

r1/-isNonZeroℚ : (a : ℚ) -> (nz : isNonZeroℚ a) -> isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz))
r1/-isNonZeroℚ =
  RationalElim.elimProp {C = \a -> (nz : isNonZeroℚ a) -> isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz))}
    (\a -> isPropΠ (\ nz -> (isProp-isNonZeroℚ (r1/ a (isNonZeroℚ->ℚInv nz)))))
    (\a nz -> rNonZero a)

NonZeroℚ : Type₀
NonZeroℚ = Σ ℚ isNonZeroℚ

_r^ℕ⁰_ : ℚ -> ℕ -> ℚ
a r^ℕ⁰ zero = 1r
a r^ℕ⁰ (suc n) = a r* (a r^ℕ⁰ n)

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


1/ℕ' : Nat⁺ -> Rational'
1/ℕ' (n , pos-n) = record
  { numerator = (ℕ->ℤ 1)
  ; denominator = (ℕ->ℤ n)
  ; NonZero-denominator = Posℕ->NonZeroℤ n pos-n
  }
  where
  Posℕ->NonZeroℤ : (n : Nat) -> (Pos' n) -> (int.NonZero (ℕ->ℤ n))
  Posℕ->NonZeroℤ (suc _) _ = (inj-l tt)

1/ℕ : Nat⁺ -> ℚ
1/ℕ n = [ 1/ℕ' n ]

1/2r : ℚ
1/2r = 1/ℕ 2⁺

1/2r' : Rational'
1/2r' = 1/ℕ' 2⁺

2r' : Rational'
2r' = record
  { numerator = (ℕ->ℤ 2)
  ; denominator = (ℕ->ℤ 1)
  ; NonZero-denominator = (inj-l tt)
  }

2r : ℚ
2r = [ 2r' ]

abstract
  2r-path-base : 1r r+ 1r == 2r
  2r-path-base = cong [_] (nd-paths->path _ _ n-path d-path)
    where
    2z-path : (int 1) i+ (int 1) == (int 2)
    2z-path = int.add1-extract-right >=> sym int.add1-extract-left >=> int.+-right-zero

    n-path : numer (1r' r+' 1r') == numer 2r'
    n-path = cong numer (r+'-eval {1r'} {1r'}) >=> (cong2 _i+_ int.*-left-one int.*-left-one) >=> 2z-path
    d-path : denom (1r' r+' 1r') == denom 2r'
    d-path = cong denom (r+'-eval {1r'} {1r'}) >=> int.*-left-one

  2r-path : (q : ℚ) -> q r+ q == 2r r* q
  2r-path q =
    cong2 _r+_ (sym (r*-left-one q)) (sym (r*-left-one q)) >=>
    sym (r*-distrib-r+-right 1r 1r q) >=>
    cong (_r* q) 2r-path-base

  2r-1/2r-path : 2r r* 1/2r == 1r
  2r-1/2r-path = eq/ (2r' r*' 1/2r') 1r' path
    where
    path : (((int 2) i* (int 1)) i* (int 1)) == (int 1) i* ((int 1) i* (int 2))
    path = int.*-commute >=> cong ((int 1) i*_) int.*-commute

  1/2r-path : (q : ℚ) -> (q r* 1/2r) r+ (q r* 1/2r) == q
  1/2r-path q = 2r-path (q r* 1/2r) >=> r*-commute 2r (q r* 1/2r) >=>
                r*-assoc q 1/2r 2r >=> cong (q r*_) (r*-commute 1/2r 2r >=> 2r-1/2r-path) >=>
                r*-right-one q

  1/2r-path' : (q : ℚ) -> (1/2r r* q) r+ (1/2r r* q) == q
  1/2r-path' q = cong2 _r+_ (r*-commute 1/2r q) (r*-commute 1/2r q) >=> 1/2r-path q


1/2ℕ'-r~ : (n : Nat⁺) -> (1/ℕ' (2⁺ *⁺ n)) r~ (1/2r' r*' 1/ℕ' n)
1/2ℕ'-r~ n =
  int.*-left-one >=> sym int-inject-*' >=>
  sym int.*-left-one >=> int.*-left (sym int.*-left-one)

abstract
  1/2ℕ-path : (n : Nat⁺) -> (1/ℕ (2⁺ *⁺ n)) == (1/2r r* 1/ℕ n)
  1/2ℕ-path n = eq/ _ _ (1/2ℕ'-r~ n)

1/ℕ-ℕ-r~ : (n : Nat⁺) -> ((1/ℕ' n) r*' (ℕ->ℚ' ⟨ n ⟩)) r~ 1r'
1/ℕ-ℕ-r~ n =
  int.*-right-one >=> int.*-left-one >=> sym int.*-right-one >=> sym int.*-left-one

abstract
  1/ℕ-ℕ-path : (n : Nat⁺) -> (1/ℕ n) r* (ℕ->ℚ ⟨ n ⟩) == 1r
  1/ℕ-ℕ-path n = eq/ _ _ (1/ℕ-ℕ-r~ n)

1/2^ℕ-path : (n : Nat) -> 1/ℕ (2⁺ ^⁺ n) == 1/2r r^ℕ⁰ n
1/2^ℕ-path zero = refl
1/2^ℕ-path (suc n) = 1/2ℕ-path (2⁺ ^⁺ n) >=> cong (1/2r r*_) (1/2^ℕ-path n)


-- Floor

ℤ* = Σ ℤ NonZero

quotientℤ : (n : ℤ) (d : ℤ*) -> ℤ
quotientℤ n (int.pos d , _) = quotient n (suc d , tt)
quotientℤ n (int.neg d , _) = (quotient (int.- n) (suc d , tt))
quotientℤ n (int.zero-int , (inj-l ()))
quotientℤ n (int.zero-int , (inj-r ()))

remainderℤ : (n : ℤ) (d : ℤ*) -> ℤ
remainderℤ n (int.pos d , _) = int ⟨ remainder n (suc d , tt) ⟩
remainderℤ n (int.neg d , _) = int.- (int ⟨ (remainder (int.- n) (suc d , tt)) ⟩)
remainderℤ n (int.zero-int , (inj-l ()))
remainderℤ n (int.zero-int , (inj-r ()))


ℤ*-* : ℤ* -> ℤ* -> ℤ*
ℤ*-* (m , nz-m) (d , nz-d) = (m int.* d , int.*-NonZero-NonZero nz-m nz-d)

private

  quotientℤ-path : (a : ℤ) (d : ℤ*) -> (quotientℤ a d int.* ⟨ d ⟩) int.+ (remainderℤ a d) == a
  quotientℤ-path a (int.pos d , _) =
    QuotientRemainder.path (quotient-remainder (suc d , tt) a)
  quotientℤ-path a (int.neg d , _) =
    int.+-left (int.minus-extract-right) >=>
    sym int.minus-distrib-+ >=>
    cong int.-_ (QuotientRemainder.path (quotient-remainder (suc d , tt) (int.- a))) >=>
    int.minus-double-inverse
  quotientℤ-path a (int.zero-int , inj-l ())
  quotientℤ-path a (int.zero-int , inj-r ())

  quotientℤ-multiple-path :
    (m : ℤ*) -> (n : ℤ) -> (d : ℤ*) ->
    quotientℤ n d == quotientℤ (⟨ m ⟩ int.* n) (ℤ*-* m d)
  quotientℤ-multiple-path m@(int.pos m' , _) n d@(int.pos d' , _) =
    quotient-multiple-path (suc m' , tt) n (suc d' , tt) >=>
    cong (quotientℤ (int.pos m' int.* n)) (ΣProp-path {x = _ , (inj-l tt)} int.isPropNonZero int-inject-*')
  quotientℤ-multiple-path m@(int.pos m' , _) n d@(int.neg d' , _) =
    quotient-multiple-path (suc m' , tt) (int.- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) (int.minus-extract-right) >=>
    cong (quotientℤ (int.pos m' int.* n)) (ΣProp-path {x = _ , (inj-r tt)} int.isPropNonZero p1)
    where
    p1 : (int.neg (d' +' (m' *' suc d'))) == (int.pos m' int.* int.neg d')
    p1 = cong int.-_ int-inject-*' >=> sym int.minus-extract-right
  quotientℤ-multiple-path m@(int.neg m' , _) n d@(int.pos d' , _) =
    cong (\x -> quotient x (suc d' , tt)) (sym (int.minus-double-inverse {n})) >=>
    quotient-multiple-path (suc m' , tt) (int.- (int.- n)) (suc d' , tt) >=>
    cong (\x -> quotient x ((suc m' , tt) *⁺ (suc d' , tt))) p2 >=>
    cong (quotientℤ (int.neg m' int.* n)) (ΣProp-path {x = _ , (inj-r tt)} int.isPropNonZero p1)
    where
    p1 : int.neg (d' +' (m' *' suc d')) == (int.neg m' int.* int.pos d')
    p1 = cong int.-_ int-inject-*' >=> sym int.minus-extract-left
    p2 : int.pos m' int.* (int.- (int.- n)) == int.- (int.neg m' int.* n)
    p2 = int.minus-extract-right >=> sym int.minus-extract-left >=> int.minus-extract-right
  quotientℤ-multiple-path m@(int.neg m' , _) n d@(int.neg d' , _) =
    quotient-multiple-path (suc m' , tt) (int.- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) (int.minus-extract-right >=> sym int.minus-extract-left) >=>
    cong (quotientℤ (int.neg m' int.* n)) (ΣProp-path {x = _ , (inj-l tt)} int.isPropNonZero p1)
    where
    p1 : int (suc m' *' suc d') == (int.neg m' int.* int.neg d')
    p1 = int-inject-*' >=> sym int.minus-double-inverse >=>
         cong int.-_ (sym int.minus-extract-right) >=>
         sym int.minus-extract-left
  quotientℤ-multiple-path (int.zero-int , inj-l ())
  quotientℤ-multiple-path (int.zero-int , inj-r ())
  quotientℤ-multiple-path (int.pos _ , _) _ (int.zero-int , inj-l ())
  quotientℤ-multiple-path (int.pos _ , _) _ (int.zero-int , inj-r ())
  quotientℤ-multiple-path (int.neg _ , _) _ (int.zero-int , inj-l ())
  quotientℤ-multiple-path (int.neg _ , _) _ (int.zero-int , inj-r ())

remainderℤ-NonNeg : (n : ℤ) (d : ℤ*) -> int.Pos ⟨ d ⟩ -> int.NonNeg (remainderℤ n d)
remainderℤ-NonNeg n (int.pos _ , _) _ = int.NonNeg-nonneg _

remainderℤ-NonPos : (n : ℤ) (d : ℤ*) -> int.Neg ⟨ d ⟩ -> int.NonPos (remainderℤ n d)
remainderℤ-NonPos n (int.neg d' , _) _ =
  int.minus-NonNeg {remainderℤ (int.- n) (int.pos d' , inj-l tt)}
                   (remainderℤ-NonNeg (int.- n) (int.pos d' , inj-l tt) _)


floor' : Rational' -> ℤ
floor' r = quotientℤ (numer r) (denom r , rNonZero r)

floor'-r~ : (x y : Rational') -> (x r~ y) -> floor' x == floor' y
floor'-r~ x y r =
  quotientℤ-multiple-path dy* nx dx* >=>
  cong2 quotientℤ n-path (ΣProp-path int.isPropNonZero d-path)
  >=> sym (quotientℤ-multiple-path dx* ny dy*)

  where
  nx = numer x
  ny = numer y
  dx = denom x
  dy = denom y
  dx* : ℤ*
  dx* = denom x , rNonZero x
  dy* : ℤ*
  dy* = denom y , rNonZero y

  n-path : dy int.* nx == dx int.* ny
  n-path = int.*-commute >=> r >=> int.*-commute

  d-path : dy int.* dx == dx int.* dy
  d-path = int.*-commute

fractional-part' : Rational' -> Rational'
fractional-part' r = record
  { numerator = (remainderℤ (numer r) (denom r , rNonZero r))
  ; denominator = (denom r)
  ; NonZero-denominator = (rNonZero r)
  }

fractional-part'-r+' : (q : Rational') -> ℤ->ℚ' (floor' q) r+' (fractional-part' q) == q
fractional-part'-r+' q = (\i -> record
  { numerator = np i
  ; denominator = dp i
  ; NonZero-denominator = isProp->PathP (\i -> int.isPropNonZero {dp i}) (rNonZero q') (rNonZero q) i
  })
  where
  q' = ℤ->ℚ' (floor' q) r+' (fractional-part' q)

  np : numer q' == numer q
  np = cong numer r+'-eval >=> int.+-right int.*-right-one >=>
       quotientℤ-path (numer q) (denom q , rNonZero q)
  dp : denom q' == denom q
  dp = cong denom r+'-eval >=> int.*-left-one

fractional-part'-preserves-r~ : (a b : Rational') -> (a r~ b) ->
                                (fractional-part' a r~ fractional-part' b)
fractional-part'-preserves-r~ a b r = ans
  where
  na = numer a
  nb = numer b
  da = denom a
  db = denom b
  da* : ℤ*
  da* = (da , rNonZero a)
  db* : ℤ*
  db* = (db , rNonZero b)

  r-path-a : (remainderℤ na da*) == na int.+ (int.- ((quotientℤ na da*) int.* da))
  r-path-a =
    sym int.+-right-zero >=>
    int.+-right (sym (int.add-minus-zero {((quotientℤ na da*) int.* da)})) >=>
    sym int.+-assoc >=>
    int.+-left (int.+-commute >=> quotientℤ-path na da*)

  r-path-b : (remainderℤ nb db*) == nb int.+ (int.- ((quotientℤ nb db*) int.* db))
  r-path-b =
    sym int.+-right-zero >=>
    int.+-right (sym (int.add-minus-zero {((quotientℤ nb db*) int.* db)})) >=>
    sym int.+-assoc >=>
    int.+-left (int.+-commute >=> quotientℤ-path nb db*)

  inner-path : (((quotientℤ na da*) int.* da) int.* db) ==
                (((quotientℤ nb db*) int.* db) int.* da)
  inner-path = int.*-assoc >=> cong2 int._*_ (floor'-r~ a b r) int.*-commute >=> sym int.*-assoc

  mid-path : (na int.+ (int.- ((quotientℤ na da*) int.* da))) int.* db ==
             (nb int.+ (int.- ((quotientℤ nb db*) int.* db))) int.* da
  mid-path =
    int.*-distrib-+ >=>
    (cong2 int._+_ r (int.minus-extract-left >=> (cong int.-_ inner-path) >=>
                      sym int.minus-extract-left)) >=>
    (sym int.*-distrib-+)

  ans : (remainderℤ na da*) int.* db == (remainderℤ nb db*) int.* da
  ans = int.*-left r-path-a >=> mid-path >=> int.*-left (sym r-path-b)

floor : Rational -> ℤ
floor = RationalElim.rec int.isSetInt floor' floor'-r~

floorℚ : Rational -> ℚ
floorℚ = ℤ->ℚ ∘ floor

fractional-part : Rational -> Rational
fractional-part = RationalElim.rec isSetRational
                    (\a -> [ fractional-part' a ])
                    (\a b r -> eq/ _ _ (fractional-part'-preserves-r~ a b r))

abstract
  fractional-part-r+ : (q : Rational) -> floorℚ q r+ (fractional-part q) == q
  fractional-part-r+ = RationalElim.elimProp (\_ -> (isSetRational _ _))
                        (\q -> cong [_] (fractional-part'-r+' q))


ℤ->ℚ-floor : (x : ℤ) -> floor (ℤ->ℚ x) == x
ℤ->ℚ-floor x = cong QuotientRemainder.q (snd isContr-QuotientRemainder qr)
  where
  qr : QuotientRemainder 1⁺ x
  qr = record
    { q = x
    ; r = (0 , (zero-<))
    ; path = int.+-right-zero >=> int.*-right-one
    }
