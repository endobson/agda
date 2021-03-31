{-# OPTIONS --cubical --safe --exact-split #-}

module rational where

open import base
open import cubical using (_∧_ ; _∨_ ; ~_)
open import equality
open import equivalence
open import functions
open import funext
open import nat
open import hlevel
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

Rational : Type₀
Rational = Rational' / _r~_

ℚ = Rational

_r+'_ : Rational' -> Rational' -> Rational'
a r+' b = record
  { numerator = ((numer a) i* (denom b)) i+ ((numer b) i* (denom a))
  ; denominator = (denom a) i* (denom b)
  ; NonZero-denominator = int.*-NonZero-NonZero (rNonZero a) (rNonZero b)
  }

nd-paths->path : (a b : Rational') -> (numer a == numer b) -> (denom a == denom b) -> a == b
nd-paths->path a b pn pd = (\i -> record
  { numerator = pn i
  ; denominator = pd i
  ; NonZero-denominator = pnz i
  })
  where
  pnz : PathP (\i -> NonZero (pd i)) (rNonZero a) (rNonZero b)
  pnz = isProp->PathP (\_ -> int.isPropNonZero) _ _

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

module RationalElim = SetQuotientElim Rational' _r~_

_r+_ : Rational -> Rational -> Rational
_r+_ = RationalElim.rec2 squash/
        (\a b -> [ a r+' b ])
        (\b a1 a2 r -> eq/ _ _ (r+'-preserves-r~₁ b a1 a2 r))
        (\a b1 b2 r -> eq/ _ _ (r+'-preserves-r~₂ a b1 b2 r))

isSetRational : isSet Rational
isSetRational = squash/

r+-commute : (a b : Rational) -> (a r+ b) == (b r+ a)
r+-commute = RationalElim.elimProp2 (\a b -> isSetRational _ _) (\a b -> cong [_] (r+'-commute a b))

0r' : Rational'
0r' = record
  { numerator = (int 0)
  ; denominator = (int 1)
  ; NonZero-denominator = tt
  }

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

r+-left-zero : (a : Rational) -> (0r r+ a) == a
r+-left-zero = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> cong [_] (r+'-left-zero a))

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

_r*_ : Rational -> Rational -> Rational
_r*_ = RationalElim.rec2 squash/
        (\a b -> [ a r*' b ])
        (\b a1 a2 r -> eq/ _ _ (r*'-preserves-r~₁ b a1 a2 r))
        (\a b1 b2 r -> eq/ _ _ (r*'-preserves-r~₂ a b1 b2 r))

r*-commute : (a b : Rational) -> (a r* b) == (b r* a)
r*-commute = RationalElim.elimProp2 (\a b -> isSetRational _ _) (\a b -> cong [_] (r*'-commute a b))

r*'-left-zero : (a : Rational') -> (0r' r*' a) r~ 0r'
r*'-left-zero a = int.*-right-one {numer (0r' r*' a)}
                  >=> int.*-left-zero {numer a}
                  >=> sym (int.*-left-zero {denom (0r' r*' a)})

r*-left-zero : (a : Rational) -> (0r r* a) == 0r
r*-left-zero = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> eq/ _ _ (r*'-left-zero a))

1r' : Rational'
1r' = record
  { numerator = (int 1)
  ; denominator = (int 1)
  ; NonZero-denominator = tt
  }

1r : Rational
1r = [ 1r' ]

r*'-left-one : (a : Rational') -> (1r' r*' a) == a
r*'-left-one a = nd-paths->path _ _ (int.*-left-one {numer a}) (int.*-left-one {denom a})

r*-left-one : (a : Rational) -> (1r r* a) == a
r*-left-one = RationalElim.elimProp (\a -> isSetRational _ _) (\a -> cong [_] (r*'-left-one a))

r*'-assoc : (a b c : Rational') -> ((a r*' b) r*' c) == (a r*' (b r*' c))
r*'-assoc a b c = nd-paths->path _ _ (int.*-assoc {numer a} {numer b} {numer c})
                                     (int.*-assoc {denom a} {denom b} {denom c})

r*-assoc : (a b c : Rational) -> ((a r* b) r* c) == (a r* (b r* c))
r*-assoc = RationalElim.elimProp3 (\a b c -> isSetRational _ _) (\a b c -> cong [_] (r*'-assoc a b c))

r+'-assoc : (a b c : Rational') -> ((a r+' b) r+' c) r~ (a r+' (b r+' c))
r+'-assoc a b c = path
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

r+-assoc : (a b c : Rational) -> ((a r+ b) r+ c) == (a r+ (b r+ c))
r+-assoc = RationalElim.elimProp3 (\a b c -> isSetRational _ _) (\a b c -> (eq/ _ _ (r+'-assoc a b c)))

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

r+-inverse : (a : Rational) -> (a r+ (r- a)) == 0r
r+-inverse = RationalElim.elimProp
             (\_ -> isSetRational _ _)
             (\a -> eq/ _ _ (r+'-inverse a))

r*-minus-extract-left : (a1 a2 : Rational) -> (r- a1) r* a2 == r- (a1 r* a2)
r*-minus-extract-left =
  RationalElim.elimProp2
    (\_ _ -> isSetRational _ _)
    (\a1 a2 -> cong [_] (nd-paths->path _ _ int.minus-extract-left refl))


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
  handle (int.nonneg (suc _)) p = subst NonZero p tt
  handle (int.neg _) p = subst NonZero p tt
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

r1/-inverse : (a : Rational) -> (i : ℚInv a) -> ((r1/ a i) r* a) == 1r
r1/-inverse = RationalElim.elimProp
               (\_ -> isPropΠ (\_ -> isSetRational _ _))
               (\ a i -> eq/ _ _ (r1/'-inverse a (ℚInv->ℚInv' _ i)))


ℤ->ℚ : Int -> Rational
ℤ->ℚ x = [ record
  { numerator = x
  ; denominator = (int 1)
  ; NonZero-denominator = tt
  } ]

ℕ->ℚ : Nat -> Rational
ℕ->ℚ n = ℤ->ℚ (ℕ->ℤ n)

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
¬isNonZeroℚ-0r b = b

isNonZeroℚ-1r : (isNonZeroℚ 1r)
isNonZeroℚ-1r = tt

isNonZeroℚ->ℚInv : {r : ℚ} -> isNonZeroℚ r -> ℚInv r
isNonZeroℚ->ℚInv nz p = ¬isNonZeroℚ-0r (subst isNonZeroℚ p nz)

Pos'->NonZeroℚ : {n : Nat} -> Pos' n -> isNonZeroℚ (ℕ->ℚ n)
Pos'->NonZeroℚ {n = (suc _)} _ = tt

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
