{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers where

open import base
open import equality
open import equivalence
open import cubical
open import functions
open import isomorphism
open import div
open import hlevel
open import nat
open import fin
open import relatively-prime
open import sigma.base
open import linear-combo
open import gcd.propositional
open import gcd.euclidean-algorithm
open import prime-gcd
open import quotient-remainder-int
open import univalence
open import relation
open import monoid
open import commutative-monoid
open import group
open import commutative-monoid.subtype
open import set-quotient renaming ([_] to s[_])

import int
import solver

open int using (int ; Int ; ℤ )
  renaming (_*_ to _i*_ ; _+_ to _i+_ ; -_ to i-_ )
open solver using (_⊗_ ; _⊕_ ; ⊖_)

record CongruentMod (n : Nat) (a b : Int) : Type₀ where
  constructor congruent-mod
  field
    n%ab : (int n) div (a i+ (i- b))

module _ {n : Nat} where
  private
    _~_ = CongruentMod n

  refl-~ : Reflexive _~_
  refl-~ {x} = (congruent-mod ((int 0) , int.*-left-zero >=> sym int.add-minus-zero))

  sym-~ : Symmetric _~_
  sym-~ {x} {y} (congruent-mod n%xy) = congruent-mod (subst (_ div_) p (div-negate n%xy))
     where
     p : (i- (x i+ (i- y))) == (y i+ (i- x))
     p = int.minus-distrib-+ >=> int.+-right int.minus-double-inverse >=> int.+-commute

  trans-~ : Transitive _~_
  trans-~ {x} {y} {z} (congruent-mod (d1 , p1)) (congruent-mod (d2 , p2)) = congruent-mod n%xz
    where
    n%xz : (int n) div (x i+ (i- z))
    n%xz = d1 i+ d2 ,
           int.*-distrib-+ >=> cong2 _i+_ p1 p2 >=> int.+-assoc >=>
           int.+-right (sym int.+-assoc >=>
                        int.+-left (int.+-commute >=> int.add-minus-zero) >=>
                        int.+-left-zero)

  isEquivRel-~ : isEquivRel _~_
  isEquivRel-~ = (equivRel refl-~ sym-~ trans-~)



ℤ/nℤ : (n : Nat) -> Type₀
ℤ/nℤ n = ℤ / (CongruentMod n)

module ℤ/nℤElim {n : Nat} = SetQuotientElim ℤ (CongruentMod n)


isSet-ℤ/nℤ : {n : Nat} -> isSet (ℤ/nℤ n)
isSet-ℤ/nℤ = squash/

module _ {n : Nat} where
  private
    _~_ = CongruentMod n

    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  private
    _z+'_ : ℤ -> ℤ -> ℤ/nℤ n
    _z+'_ x y = [ x i+ y ]

    i+-~₁ : (y x1 x2 : ℤ) -> (x1 ~ x2) -> (x1 i+ y) ~ (x2 i+ y)
    i+-~₁ y x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : (x1 i+ (i- x2)) == ((x1 i+ y) i+ (i- (x2 i+ y)))
      path = solver.IntSolver.solve 3
             (\ y x1 x2 ->
                (x1 ⊕ (⊖ x2)) ,
                ((x1 ⊕ y) ⊕ (⊖ (x2 ⊕ y))))
             refl y x1 x2

      d : (int n) div ((x1 i+ y) i+ (i- (x2 i+ y)))
      d = subst ((int n) div_) path n%ab

    i+-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> (x i+ y1) ~ (x i+ y2)
    i+-~₂ y x1 x2 c =
      subst2 _~_ int.+-commute int.+-commute (i+-~₁ y x1 x2 c)


    z+'-~₁ : (x1 x2 y : ℤ) -> (x1 ~ x2) -> [ x1 i+ y ] == [ x2 i+ y ]
    z+'-~₁ x1 x2 y c = eq/ _ _ (i+-~₁ y x1 x2 c)

    z+'-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> [ x i+ y1 ] == [ x i+ y2 ]
    z+'-~₂ x y1 y2 c = eq/ _ _ (i+-~₂ x y1 y2 c)

  _z+_ : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
  _z+_ = ℤ/nℤElim.rec2 isSet-ℤ/nℤ _z+'_ z+'-~₁ z+'-~₂

  private
    _z*'_ : ℤ -> ℤ -> ℤ/nℤ n
    _z*'_ x y = [ x i* y ]

    i*-~₁ : (y x1 x2 : ℤ) -> (x1 ~ x2) -> (x1 i* y) ~ (x2 i* y)
    i*-~₁ y x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : ((x1 i+ (i- x2)) i* y) == ((x1 i* y) i+ (i- (x2 i* y)))
      path = solver.IntSolver.solve 3
             (\ y x1 x2 ->
                ((x1 ⊕ (⊖ x2)) ⊗ y) ,
                ((x1 ⊗ y) ⊕ (⊖ (x2 ⊗ y))))
             refl y x1 x2

      d2 : (int n) div ((x1 i+ (i- x2)) i* y)
      d2 = div-mult' n%ab y

      d : (int n) div ((x1 i* y) i+ (i- (x2 i* y)))
      d = subst ((int n) div_) path d2

    i*-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> (x i* y1) ~ (x i* y2)
    i*-~₂ y x1 x2 c =
      subst2 _~_ int.*-commute int.*-commute (i*-~₁ y x1 x2 c)


    z*'-~₁ : (x1 x2 y : ℤ) -> (x1 ~ x2) -> [ x1 i* y ] == [ x2 i* y ]
    z*'-~₁ x1 x2 y c = eq/ _ _ (i*-~₁ y x1 x2 c)

    z*'-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> [ x i* y1 ] == [ x i* y2 ]
    z*'-~₂ x y1 y2 c = eq/ _ _ (i*-~₂ x y1 y2 c)

  _z*_ : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
  _z*_ = ℤ/nℤElim.rec2 isSet-ℤ/nℤ _z*'_ z*'-~₁ z*'-~₂

  private
    z-'_ : ℤ -> ℤ/nℤ n
    z-'_ x = [ i- x ]

    i--~ : (x1 x2 : ℤ) -> (x1 ~ x2) -> (i- x1) ~ (i- x2)
    i--~ x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : (i- (x1 i+ (i- x2))) == ((i- x1) i+ (i- (i- x2)))
      path = solver.IntSolver.solve 2
             (\ x1 x2 ->
                (⊖ (x1 ⊕ (⊖ x2))) ,
                ((⊖ x1) ⊕ (⊖ (⊖ x2))))
             refl x1 x2

      d : (int n) div ((i- x1) i+ (i- (i- x2)))
      d = subst ((int n) div_) path (div-negate n%ab)


    z-'-~ : (x1 x2 : ℤ) -> (x1 ~ x2) -> [ i- x1 ] == [ i- x2 ]
    z-'-~ x1 x2 c = eq/ _ _ (i--~ x1 x2 c)

  z-_ : ℤ/nℤ n -> ℤ/nℤ n
  z-_ = ℤ/nℤElim.rec isSet-ℤ/nℤ z-'_ z-'-~

module _ (n⁺ : Nat⁺) where
  private
    n = ⟨ n⁺ ⟩
    _~_ = CongruentMod n

    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  repr : ℤ -> Fin n
  repr x = QuotientRemainder.r (quotient-remainder n⁺ x)

  repr~ : (x y : ℤ) -> (x ~ y) -> repr x == repr y
  repr~ x y (congruent-mod (d , p)) = ans
    where
    qrx = (quotient-remainder n⁺ x)
    qry = (quotient-remainder n⁺ y)
    module qrx = QuotientRemainder qrx
    module qry = QuotientRemainder qry
    ni = int n

    check-p : d i* ni == x i+ (i- y)
    check-p = p

    x-path : qrx.q i* ni i+ qrx.ri == x
    x-path = qrx.path

    y-path : qry.q i* ni i+ qry.ri == y
    y-path = qry.path

    x-path2 : (d i+ qry.q) i* ni i+ qry.ri == x
    x-path2 =
      begin
        (d i+ qry.q) i* ni i+ qry.ri
      ==< int.+-left int.*-distrib-+ >=> int.+-assoc >
        (d i* ni) i+ ((qry.q i* ni) i+ qry.ri)
      ==< cong2 _i+_ p y-path >
        (x i+ (i- y)) i+ y
      ==< int.+-assoc >=> int.+-right (int.+-commute >=> int.add-minus-zero) >=> int.+-right-zero >
        x
      end

    qrx2 : QuotientRemainder n⁺ x
    qrx2 = record { q = d i+ qry.q ; r = qry.r ; path = x-path2 }

    ans : qrx.r == qry.r
    ans = cong QuotientRemainder.r (isProp-QuotientRemainder qrx qrx2)

  ℤ/nℤ->representative : ℤ/nℤ n -> Fin n
  ℤ/nℤ->representative = ℤ/nℤElim.rec isSetFin repr repr~

  representative->ℤ/nℤ : Fin n -> ℤ/nℤ n
  representative->ℤ/nℤ (i , _) = [ (int i) ]

  private
    rep->ℤ/nℤ->rep : (i : Fin n) -> (ℤ/nℤ->representative (representative->ℤ/nℤ i)) == i
    rep->ℤ/nℤ->rep i = cong QuotientRemainder.r (isContr-QuotientRemainder .snd qr)
      where
      qr : QuotientRemainder n⁺ (int (Fin.i i))
      qr = record { q = (int 0) ; r = i ; path = int.+-left int.*-left-zero >=> int.+-left-zero }

    ℤ/nℤ->rep->ℤ/nℤ : (i : ℤ/nℤ n) -> (representative->ℤ/nℤ (ℤ/nℤ->representative i)) == i
    ℤ/nℤ->rep->ℤ/nℤ = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
      where
      handle : (i : ℤ) -> (representative->ℤ/nℤ (ℤ/nℤ->representative [ i ])) == [ i ]
      handle i = sym (eq/ _ _ r)
        where
        module qr = QuotientRemainder (quotient-remainder n⁺ i)
        r : i ~ (int (Fin.i qr.r))
        r = congruent-mod (qr.q ,
              sym int.+-right-zero >=> int.+-right (sym (int.add-minus-zero)) >=>
              sym int.+-assoc >=> int.+-left qr.path)

  ℤ/nℤ-Fin-eq : ℤ/nℤ n ≃ Fin n
  ℤ/nℤ-Fin-eq = isoToEquiv i
    where
    open Iso
    i : Iso (ℤ/nℤ n) (Fin n)
    i .fun = ℤ/nℤ->representative
    i .inv = representative->ℤ/nℤ
    i .rightInv = rep->ℤ/nℤ->rep
    i .leftInv = ℤ/nℤ->rep->ℤ/nℤ

0# : {n : Nat} -> ℤ/nℤ n
0# = s[ (int 0) ]

1# : {n : Nat} -> ℤ/nℤ n
1# = s[ (int 1) ]

abstract
  _z*a_ : {n : Nat} -> ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
  _z*a_ = _z*_

  z*a-eval : {n : Nat} -> {x y : ℤ/nℤ n} -> (x z*a y) == (x z* y)
  z*a-eval = refl


record Unit' {n : Nat} (x : ℤ/nℤ n) : Type₀ where
  field
    inv : ℤ/nℤ n
    path-a : (x z*a inv) == 1#

  path : (x z* inv) == 1#
  path = sym z*a-eval >=> path-a

unit' : {n : Nat} -> (x y : ℤ/nℤ n) -> (x z* y) == 1# -> Unit' x
unit' x y p = record { inv = y ; path-a = z*a-eval >=> p }



module _ {n : Nat} where
  private
    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  z+-left-zero : (i : ℤ/nℤ n) -> 0# z+ i == i
  z+-left-zero = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] int.+-left-zero)

  z*-left-zero : (i : ℤ/nℤ n) -> 0# z* i == 0#
  z*-left-zero = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] int.*-left-zero)

  z*-left-one : (i : ℤ/nℤ n) -> 1# z* i == i
  z*-left-one = ℤ/nℤElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] int.*-left-one)

  z+-assoc : (i j k : ℤ/nℤ n) -> (i z+ j) z+ k == i z+ (j z+ k)
  z+-assoc = ℤ/nℤElim.elimProp3 (\_ _ _ -> isSet-ℤ/nℤ _ _) (\_ _ _ -> cong [_] int.+-assoc)

  z+-commute : (i j : ℤ/nℤ n) -> i z+ j == j z+ i
  z+-commute = ℤ/nℤElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> cong [_] int.+-commute)

  z*-assoc : (i j k : ℤ/nℤ n) -> (i z* j) z* k == i z* (j z* k)
  z*-assoc = ℤ/nℤElim.elimProp3 (\_ _ _ -> isSet-ℤ/nℤ _ _) (\_ _ _ -> cong [_] int.*-assoc)

  z*-commute : (i j : ℤ/nℤ n) -> i z* j == j z* i
  z*-commute = ℤ/nℤElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> cong [_] int.*-commute)

  Unit : ℤ/nℤ n -> Type₀
  Unit x = Σ[ y ∈ ℤ/nℤ n ] ((x z* y) == 1#)


  isProp-Unit : {x : ℤ/nℤ n} -> isProp (Unit x)
  isProp-Unit {x} (y1 , p1) (y2 , p2) =
    ΣProp-path (isSet-ℤ/nℤ _ _)
      (sym (z*-left-one y1) >=>
       (cong (_z* y1) (sym p2 >=> z*-commute x y2)) >=>
       z*-assoc y2 x y1 >=> z*-commute y2 (x z* y1) >=>
       (cong (_z* y2) p1) >=> z*-left-one y2)

  unit-one : Unit 1#
  unit-one = 1# , z*-left-one _

  unit'-one : Unit' 1#
  unit'-one = unit' _ 1# (z*-left-one _)

  u*-closed : {i j : ℤ/nℤ n} -> Unit i -> Unit j -> Unit (i z* j)
  u*-closed {i} {j}  (1/i , pi) (1/j , pj) = 1/i z* 1/j , p
    where
    p : (i z* j) z* (1/i z* 1/j) == 1#
    p = cong (_z* (1/i z* 1/j)) (z*-commute i j) >=>
        z*-assoc j i (1/i z* 1/j) >=> (cong (j z*_) (sym (z*-assoc i 1/i 1/j))) >=>
        cong (j z*_) (cong (_z* 1/j) pi >=> z*-left-one 1/j) >=> pj

  u'*-closed : {i j : ℤ/nℤ n} -> Unit' i -> Unit' j -> Unit' (i z* j)
  u'*-closed {i} {j} ui uj = unit' _ (1/i z* 1/j) p
    where
    1/i = Unit'.inv ui
    pi = Unit'.path ui
    1/j = Unit'.inv uj
    pj = Unit'.path uj

    p : (i z* j) z* (1/i z* 1/j) == 1#
    p = cong (_z* (1/i z* 1/j)) (z*-commute i j) >=>
        z*-assoc j i (1/i z* 1/j) >=> (cong (j z*_) (sym (z*-assoc i 1/i 1/j))) >=>
        cong (j z*_) (cong (_z* 1/j) pi >=> z*-left-one 1/j) >=> pj



  MonoidStr-ℤ/nℤ-* : Monoid (ℤ/nℤ n)
  MonoidStr-ℤ/nℤ-* = record
    { ε = 1#
    ; _∙_ = _z*_
    ; ∙-assoc = \{x} {y} {z} -> z*-assoc x y z
    ; ∙-left-ε = \{x} -> z*-left-one x
    ; ∙-right-ε = \{x} -> z*-commute x 1#  >=> z*-left-one x
    }

  CommMonoidStr-ℤ/nℤ-* : CommMonoid (ℤ/nℤ n)
  CommMonoidStr-ℤ/nℤ-* = record
    { monoid = MonoidStr-ℤ/nℤ-*
    ; ∙-commute = \{x} {y} -> z*-commute x y
    ; isSet-Domain = isSet-ℤ/nℤ
    }


isProp-Unit' : {n : Nat} {x : ℤ/nℤ n} -> isProp (Unit' x)
isProp-Unit' {n} {x} u1 u2 = (\i -> record
  { inv = inv-path i
  ; path-a = path-a-path i
  })
  where
  module u1 = Unit' u1
  module u2 = Unit' u2

  inv-path : u1.inv == u2.inv
  inv-path =
    (sym (z*-left-one u1.inv) >=>
    (cong (_z* u1.inv) (sym u2.path >=> z*-commute x u2.inv)) >=>
    z*-assoc u2.inv x u1.inv >=> z*-commute u2.inv (x z* u1.inv) >=>
    (cong (_z* u2.inv) u1.path) >=> z*-left-one u2.inv)

  path-a-path : PathP (\i -> x z*a (inv-path i) == 1#) u1.path-a u2.path-a
  path-a-path = isProp->PathP (\_ -> isSet-ℤ/nℤ _ _) u1.path-a u2.path-a



ℤ/nℤ* : (n : Nat) -> Type₀
ℤ/nℤ* n = Σ (ℤ/nℤ n) Unit'

isSet-ℤ/nℤ* : {n : Nat} -> isSet (ℤ/nℤ* n)
isSet-ℤ/nℤ* = isSetΣ isSet-ℤ/nℤ (\_ -> (isProp->isSet isProp-Unit'))

module _ {n : Nat} where

  _u*_ : ℤ/nℤ* n -> ℤ/nℤ* n -> ℤ/nℤ* n
  (i , ui) u* (j , uj) = i z* j , u'*-closed {n} {i} {j} ui uj

  z1/ : ℤ/nℤ* n -> ℤ/nℤ* n
  z1/ (x , u) = u.inv , (unit' _ x (z*-commute u.inv x >=> u.path))
    where
    module u = Unit' u

  z1/-left-inverse : (x : ℤ/nℤ* n) -> (z1/ x) u* x == (1# , unit'-one)
  z1/-left-inverse (x , u) =
    ΣProp-path isProp-Unit' (z*-commute u.inv x >=> u.path)
    where
    module u = Unit' u


CommMonoidStr-ℤ/nℤ* : {n : Nat} -> CommMonoid (ℤ/nℤ* n)
CommMonoidStr-ℤ/nℤ* {n} =
  SubCommMonoidStr (\x -> isProp-Unit' {n} {x}) CommMonoidStr-ℤ/nℤ-* unit'-one
                                       (\{i} {j} -> u'*-closed {n} {i} {j})


GroupStr-ℤ/nℤ* : {n : Nat} -> GroupStr (ℤ/nℤ* n)
GroupStr-ℤ/nℤ* {n} = record
  { comm-monoid = CommMonoidStr-ℤ/nℤ*
  ; inverse = z1/
  ; ∙-left-inverse = \ {x} -> z1/-left-inverse x
  }


module _ {n : Nat} where



module _ (n⁺ : Nat⁺) where
  private
    n = ⟨ n⁺ ⟩
    pos-n = snd n⁺
    _~_ = CongruentMod n

    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  isPropValued-~ : isPropValued _~_
  isPropValued-~ a b (congruent-mod n%ab1) (congruent-mod n%ab2) =
    cong congruent-mod (isPropDiv₁ (int.Pos->NonZero (int.Pos'->Pos pos-n)) n%ab1 n%ab2)


  CoprimeN' : (x : ℤ/nℤ n) -> hProp ℓ-zero
  CoprimeN' = ℤ/nℤElim.rec isSet-hProp
                (\ x -> RelativelyPrime (int n) x , isProp-RelativelyPrime)
                (\ x y r -> ΣProp-path (isProp-isOfHLevel 1) (rp-eq x y r))
    where
    rp-f : (x y : ℤ) -> (x ~ y) -> RelativelyPrime (int n) x -> RelativelyPrime (int n) y
    rp-f x y (congruent-mod n%xy) rp-x d nn-d d%n d%y = rp-x d nn-d d%n d%x
      where
      d%xyy : d div ((x i+ (i- y)) i+ y)
      d%xyy = div-sum (div-trans d%n n%xy) d%y
      d%x : d div x
      d%x = subst (d div_)
            (int.+-assoc >=>
             int.+-right (int.+-commute >=> int.add-minus-zero) >=>
             int.+-right-zero)
            d%xyy


    abstract
      rp-eq : (x y : ℤ) -> (x ~ y) -> RelativelyPrime (int n) x == RelativelyPrime (int n) y
      rp-eq x y r = ua (isoToEquiv i)
        where
        open Iso
        i : Iso (RelativelyPrime (int n) x) (RelativelyPrime (int n) y)
        i .fun = rp-f x y r
        i .inv = rp-f y x (sym-~ r)
        i .rightInv _ = isProp-RelativelyPrime _ _
        i .leftInv _ = isProp-RelativelyPrime _ _


  CoprimeN : (x : ℤ/nℤ n) -> Type₀
  CoprimeN x = fst (CoprimeN' x)
  isProp-CoprimeN : {x : ℤ/nℤ n} -> isProp (CoprimeN x)
  isProp-CoprimeN {x} = snd (CoprimeN' x)

  module _ where
    unit->coprime' : (x y : ℤ/nℤ n) -> (x z* y == 1#) -> (CoprimeN x)
    unit->coprime' = ℤ/nℤElim.elimProp2 (\x y -> (isPropΠ (\_ -> isProp-CoprimeN {x}))) handle
      where
      handle : (x y : ℤ) -> ([ x i* y ] == 1#) -> (CoprimeN [ x ])
      handle x y p d nn-d d%n d%x = div-one->one nn-d d%1
        where
        c : (int 1) ~ (x i* y)
        c = sym-~ (ℤ/nℤElim.pathRec isPropValued-~ isEquivRel-~ _ _ p)

        d%1-xy : d div ((int 1) i+ (i- (x i* y)))
        d%1-xy = div-trans d%n (CongruentMod.n%ab c)

        d%xy : d div (x i* y)
        d%xy = div-mult' d%x y

        xy-path : ((int 1) i+ (i- (x i* y))) i+ (x i* y) == (int 1)
        xy-path = int.+-assoc >=> int.+-right (int.+-commute >=> int.add-minus-zero) >=>
                  int.+-right-zero

        d%1 : d div (int 1)
        d%1 = subst (d div_) xy-path (div-sum d%1-xy d%xy)

    unit->coprime : (x : ℤ/nℤ n) -> (Unit x) -> (CoprimeN x)
    unit->coprime x (y , p) = unit->coprime' x y p


    lc->unit : {x : ℤ} -> LinearCombination (int n) x (int 1) -> Unit [ x ]
    lc->unit {x} lc = [ y ] , eq/ (x i* y) (int 1) (congruent-mod n%xy-1)
      where
      module lc = LinearCombination lc

      y : Int
      y = lc.y

      path : (i- lc.x) i* (int n) == x i* lc.y i+ (i- (int 1))
      path = minus-extract-left >=>
             cong -_ (sym +-right-zero >=> +-right (sym (add-minus-zero {lc.y i* x})) >=>
                      sym +-assoc >=> +-left lc.path >=> +-commute) >=>
             minus-distrib-+ >=> +-left minus-double-inverse >=>
             +-left *-commute
        where
        open int

      n%xy-1 : (int n) div (x i* y i+ (i- (int 1)))
      n%xy-1 = (i- lc.x) , path

    coprime->unit : (x : ℤ/nℤ n) -> (CoprimeN x) -> (Unit x)
    coprime->unit = ℤ/nℤElim.elimProp (\x -> (isPropΠ (\_ -> isProp-Unit {x = x}))) handle
      where
      handle : (x : ℤ) -> (RelativelyPrime (int n) x) -> (Unit [ x ])
      handle x rp = lc->unit (gcd->linear-combo (relatively-prime->gcdⁱ rp))

  module _ where
    unit'->coprime : (x : ℤ/nℤ n) -> (Unit' x) -> (CoprimeN x)
    unit'->coprime x u = unit->coprime' x u.inv u.path
      where
      module u = Unit' u


    lc->unit' : {x : ℤ} -> LinearCombination (int n) x (int 1) -> Unit' [ x ]
    lc->unit' {x} lc = unit' [ x ] [ y ] (eq/ (x i* y) (int 1) (congruent-mod n%xy-1))
      where
      module lc = LinearCombination lc

      y : Int
      y = lc.y

      path : (i- lc.x) i* (int n) == x i* lc.y i+ (i- (int 1))
      path = minus-extract-left >=>
             cong -_ (sym +-right-zero >=> +-right (sym (add-minus-zero {lc.y i* x})) >=>
                      sym +-assoc >=> +-left lc.path >=> +-commute) >=>
             minus-distrib-+ >=> +-left minus-double-inverse >=>
             +-left *-commute
        where
        open int

      n%xy-1 : (int n) div (x i* y i+ (i- (int 1)))
      n%xy-1 = (i- lc.x) , path

    coprime->unit' : (x : ℤ/nℤ n) -> (CoprimeN x) -> (Unit' x)
    coprime->unit' = ℤ/nℤElim.elimProp (\x -> (isPropΠ (\_ -> isProp-Unit'))) handle
      where
      handle : (x : ℤ) -> (RelativelyPrime (int n) x) -> (Unit' [ x ])
      handle x rp = lc->unit' (gcd->linear-combo (relatively-prime->gcdⁱ rp))



Unit-Unit'-eq : {n : Nat} -> (x : ℤ/nℤ n) -> (Unit x) ≃ (Unit' x)
Unit-Unit'-eq x = isoToEquiv ui
  where
  open Iso
  ui : Iso (Unit x) (Unit' x)
  ui .fun (y , p) = unit' x y p
  ui .inv u = u.inv , u.path
    where
    module u = Unit' u
  ui .rightInv u = isProp-Unit' _ _
  ui .leftInv u = isProp-Unit {x = x} _ u


module _ (n⁺ : Nat⁺) where
  private
    n = ⟨ n⁺ ⟩

  Unit-CoprimeN-eq : (x : ℤ/nℤ n) -> (Unit' x) ≃ (CoprimeN n⁺ x)
  Unit-CoprimeN-eq x = isoToEquiv i
    where
    open Iso
    i : Iso (Unit' x) (CoprimeN n⁺ x)
    i .fun = unit'->coprime n⁺ x
    i .inv = coprime->unit' n⁺ x
    i .rightInv c = isProp-CoprimeN n⁺ {x} _ c
    i .leftInv u = isProp-Unit' _ u
