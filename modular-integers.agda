{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers where

open import additive-group hiding (0#)
open import additive-group.instances.int
open import base
open import commutative-monoid
open import commutative-monoid.subtype
open import equality
open import equivalence
open import fin
open import gcd.euclidean-algorithm
open import group
open import hlevel
open import int
open import int.division
open import isomorphism
open import linear-combo
open import monoid
open import nat
open import prime-gcd
open import quotient-remainder-int
open import relation
open import relatively-prime
open import ring
open import ring.implementations.int
open import semiring hiding (1#)
open import semiring.division
open import ring.division
open import set-quotient renaming ([_] to s[_])
open import sigma.base
open import univalence
open import truncation

import solver
open solver using (_⊗_ ; _⊕_ ; ⊖_)
open EqReasoning

record CongruentMod (n : Nat) (a b : Int) : Type₀ where
  constructor congruent-mod
  field
    n%ab : (int n) div (a + (- b))

module _ {n : Nat} where
  private
    _~_ = CongruentMod n

  refl-~ : Reflexive _~_
  refl-~ {x} = congruent-mod (∣ (int 0) , *-left-zero >=> sym int.add-minus-zero ∣)

  sym-~ : Symmetric _~_
  sym-~ {x} {y} (congruent-mod n%xy) = congruent-mod (subst (_ div_) p (div-negate n%xy))
     where
     p : (- (x + (- y))) == (y + (- x))
     p = int.minus-distrib-+ >=> +-right minus-double-inverse >=> +-commute

  trans-~ : Transitive _~_
  trans-~ {x} {y} {z} (congruent-mod %1 ) (congruent-mod %2) =
    congruent-mod (∥-map2 handle %1 %2)
    where
    handle : (int n) div' (x + (- y)) -> (int n) div' (y + (- z)) -> (int n) div' (x + (- z))
    handle (d1 , p1) (d2 , p2) =
      d1 + d2 ,
      *-distrib-+-right >=> cong2 _+_ p1 p2 >=> +-assoc >=>
      +-right (sym +-assoc >=>
               +-left (+-commute >=> int.add-minus-zero) >=>
               +-left-zero)

  isEquivRel-~ : isEquivRel _~_
  isEquivRel-~ = (equivRel refl-~ sym-~ trans-~)



ℤ/nℤ : (n : Nat) -> Type₀
ℤ/nℤ n = ℤ / (CongruentMod n)

isSet-ℤ/nℤ : {n : Nat} -> isSet (ℤ/nℤ n)
isSet-ℤ/nℤ = squash/

module _ {n : Nat} where
  private
    _~_ = CongruentMod n

    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  private
    _z+'_ : ℤ -> ℤ -> ℤ/nℤ n
    _z+'_ x y = [ x + y ]

    i+-~₁ : (y x1 x2 : ℤ) -> (x1 ~ x2) -> (x1 + y) ~ (x2 + y)
    i+-~₁ y x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : (x1 + (- x2)) == ((x1 + y) + (- (x2 + y)))
      path = solver.IntSolver.solve 3
             (\ y x1 x2 ->
                (x1 ⊕ (⊖ x2)) ,
                ((x1 ⊕ y) ⊕ (⊖ (x2 ⊕ y))))
             refl y x1 x2

      d : (int n) div ((x1 + y) + (- (x2 + y)))
      d = subst ((int n) div_) path n%ab

    i+-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> (x + y1) ~ (x + y2)
    i+-~₂ y x1 x2 c =
      subst2 _~_ +-commute +-commute (i+-~₁ y x1 x2 c)


    z+'-~₁ : (x1 x2 y : ℤ) -> (x1 ~ x2) -> [ x1 + y ] == [ x2 + y ]
    z+'-~₁ x1 x2 y c = eq/ _ _ (i+-~₁ y x1 x2 c)

    z+'-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> [ x + y1 ] == [ x + y2 ]
    z+'-~₂ x y1 y2 c = eq/ _ _ (i+-~₂ x y1 y2 c)

  _z+_ : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
  _z+_ = SetQuotientElim.rec2 isSet-ℤ/nℤ _z+'_ z+'-~₁ z+'-~₂

  private
    _z*'_ : ℤ -> ℤ -> ℤ/nℤ n
    _z*'_ x y = [ x * y ]

    i*-~₁ : (y x1 x2 : ℤ) -> (x1 ~ x2) -> (x1 * y) ~ (x2 * y)
    i*-~₁ y x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : ((x1 + (- x2)) * y) == ((x1 * y) + (- (x2 * y)))
      path = solver.IntSolver.solve 3
             (\ y x1 x2 ->
                ((x1 ⊕ (⊖ x2)) ⊗ y) ,
                ((x1 ⊗ y) ⊕ (⊖ (x2 ⊗ y))))
             refl y x1 x2

      d2 : (int n) div ((x1 + (- x2)) * y)
      d2 = div-*ʳ n%ab y

      d : (int n) div ((x1 * y) + (- (x2 * y)))
      d = subst ((int n) div_) path d2

    i*-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> (x * y1) ~ (x * y2)
    i*-~₂ y x1 x2 c =
      subst2 _~_ *-commute *-commute (i*-~₁ y x1 x2 c)


    z*'-~₁ : (x1 x2 y : ℤ) -> (x1 ~ x2) -> [ x1 * y ] == [ x2 * y ]
    z*'-~₁ x1 x2 y c = eq/ _ _ (i*-~₁ y x1 x2 c)

    z*'-~₂ : (x y1 y2 : ℤ) -> (y1 ~ y2) -> [ x * y1 ] == [ x * y2 ]
    z*'-~₂ x y1 y2 c = eq/ _ _ (i*-~₂ x y1 y2 c)

  _z*_ : ℤ/nℤ n -> ℤ/nℤ n -> ℤ/nℤ n
  _z*_ = SetQuotientElim.rec2 isSet-ℤ/nℤ _z*'_ z*'-~₁ z*'-~₂

  private
    z-'_ : ℤ -> ℤ/nℤ n
    z-'_ x = [ - x ]

    i--~ : (x1 x2 : ℤ) -> (x1 ~ x2) -> (- x1) ~ (- x2)
    i--~ x1 x2 (congruent-mod n%ab) = (congruent-mod d)
      where
      path : (- (x1 + (- x2))) == ((- x1) + (- (- x2)))
      path = solver.IntSolver.solve 2
             (\ x1 x2 ->
                (⊖ (x1 ⊕ (⊖ x2))) ,
                ((⊖ x1) ⊕ (⊖ (⊖ x2))))
             refl x1 x2

      d : (int n) div ((- x1) + (- (- x2)))
      d = subst ((int n) div_) path (div-negate n%ab)


    z-'-~ : (x1 x2 : ℤ) -> (x1 ~ x2) -> [ - x1 ] == [ - x2 ]
    z-'-~ x1 x2 c = eq/ _ _ (i--~ x1 x2 c)

  z-_ : ℤ/nℤ n -> ℤ/nℤ n
  z-_ = SetQuotientElim.rec isSet-ℤ/nℤ z-'_ z-'-~

module _ (n⁺ : Nat⁺) where
  private
    n = ⟨ n⁺ ⟩
    _~_ = CongruentMod n

    [_] : ℤ -> ℤ/nℤ n
    [_] = s[_]

  repr : ℤ -> Fin n
  repr x = QuotientRemainder.r (quotient-remainder n⁺ x)

  repr~ : (x y : ℤ) -> (x ~ y) -> repr x == repr y
  repr~ x y (congruent-mod n%diff) =
    unsquash (isSetFin _ _) (∥-map ans n%diff)
    where
    module _ ((d , p) : (int n) div' (x + (- y))) where
      qrx = (quotient-remainder n⁺ x)
      qry = (quotient-remainder n⁺ y)
      module qrx = QuotientRemainder qrx
      module qry = QuotientRemainder qry
      ni = int n

      check-p : d * ni == x + (- y)
      check-p = p

      x-path : qrx.q * ni + qrx.ri == x
      x-path = qrx.path

      y-path : qry.q * ni + qry.ri == y
      y-path = qry.path

      x-path2 : (d + qry.q) * ni + qry.ri == x
      x-path2 =
        begin
          (d + qry.q) * ni + qry.ri
        ==< +-left *-distrib-+-right >=> +-assoc >
          (d * ni) + ((qry.q * ni) + qry.ri)
        ==< cong2 _+_ p y-path >
          (x + (- y)) + y
        ==< +-assoc >=> +-right (+-commute >=> int.add-minus-zero) >=> +-right-zero >
          x
        end

      qrx2 : QuotientRemainder n⁺ x
      qrx2 = record { q = d + qry.q ; r = qry.r ; path = x-path2 }

      ans : qrx.r == qry.r
      ans = cong QuotientRemainder.r (isProp-QuotientRemainder qrx qrx2)

  ℤ/nℤ->representative : ℤ/nℤ n -> Fin n
  ℤ/nℤ->representative = SetQuotientElim.rec isSetFin repr repr~

  representative->ℤ/nℤ : Fin n -> ℤ/nℤ n
  representative->ℤ/nℤ (i , _) = [ (int i) ]

  private
    rep->ℤ/nℤ->rep : (i : Fin n) -> (ℤ/nℤ->representative (representative->ℤ/nℤ i)) == i
    rep->ℤ/nℤ->rep i = cong QuotientRemainder.r (isContr-QuotientRemainder .snd qr)
      where
      qr : QuotientRemainder n⁺ (int (Fin.i i))
      qr = record { q = (int 0) ; r = i ; path = +-left *-left-zero >=> +-left-zero }

    ℤ/nℤ->rep->ℤ/nℤ : (i : ℤ/nℤ n) -> (representative->ℤ/nℤ (ℤ/nℤ->representative i)) == i
    ℤ/nℤ->rep->ℤ/nℤ = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
      where
      handle : (i : ℤ) -> (representative->ℤ/nℤ (ℤ/nℤ->representative [ i ])) == [ i ]
      handle i = sym (eq/ _ _ r)
        where
        module qr = QuotientRemainder (quotient-remainder n⁺ i)
        r : i ~ (int (Fin.i qr.r))
        r = congruent-mod ∣ (qr.q ,
              sym +-right-zero >=> +-right (sym (int.add-minus-zero)) >=>
              sym +-assoc >=> +-left qr.path) ∣

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
  z+-left-zero = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] +-left-zero)

  z*-left-zero : (i : ℤ/nℤ n) -> 0# z* i == 0#
  z*-left-zero = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] *-left-zero)

  z*-left-one : (i : ℤ/nℤ n) -> 1# z* i == i
  z*-left-one = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) (\_ -> cong [_] *-left-one)

  z+-assoc : (i j k : ℤ/nℤ n) -> (i z+ j) z+ k == i z+ (j z+ k)
  z+-assoc = SetQuotientElim.elimProp3 (\_ _ _ -> isSet-ℤ/nℤ _ _) (\_ _ _ -> cong [_] +-assoc)

  z+-commute : (i j : ℤ/nℤ n) -> i z+ j == j z+ i
  z+-commute = SetQuotientElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> cong [_] +-commute)

  z*-assoc : (i j k : ℤ/nℤ n) -> (i z* j) z* k == i z* (j z* k)
  z*-assoc = SetQuotientElim.elimProp3 (\_ _ _ -> isSet-ℤ/nℤ _ _) (\_ _ _ -> cong [_] *-assoc)

  z*-commute : (i j : ℤ/nℤ n) -> i z* j == j z* i
  z*-commute = SetQuotientElim.elimProp2 (\_ _ -> isSet-ℤ/nℤ _ _) (\_ _ -> cong [_] *-commute)

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
    ; isSet-Domain = isSet-ℤ/nℤ
    }

  CommMonoidStr-ℤ/nℤ-* : CommMonoid (ℤ/nℤ n)
  CommMonoidStr-ℤ/nℤ-* = record
    { monoid = MonoidStr-ℤ/nℤ-*
    ; ∙-commute = \{x} {y} -> z*-commute x y
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
  path-a-path = isProp->PathP (\_ -> isSet-ℤ/nℤ _ _)



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

  z1/-right-inverse : (x : ℤ/nℤ* n) -> x u* (z1/ x) == (1# , unit'-one)
  z1/-right-inverse (x , u) =
    ΣProp-path isProp-Unit' u.path
    where
    module u = Unit' u

CommMonoidStr-ℤ/nℤ* : {n : Nat} -> CommMonoid (ℤ/nℤ* n)
CommMonoidStr-ℤ/nℤ* {n} =
  SubCommMonoidStr (\x -> isProp-Unit' {n} {x}) CommMonoidStr-ℤ/nℤ-* unit'-one
                                       (\{i} {j} -> u'*-closed {n} {i} {j})


AbGroupStr-ℤ/nℤ* : {n : Nat} -> AbGroupStr (ℤ/nℤ* n)
AbGroupStr-ℤ/nℤ* {n} = record
  { comm-monoid = CommMonoidStr-ℤ/nℤ*
  ; inverse = z1/
  ; ∙-left-inverse = \ {x} -> z1/-left-inverse x
  ; ∙-right-inverse = \ {x} -> z1/-right-inverse x
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
    cong congruent-mod (isPropDiv n%ab1 n%ab2)


  CoprimeN' : (x : ℤ/nℤ n) -> hProp ℓ-zero
  CoprimeN' = SetQuotientElim.rec isSet-hProp
                (\ x -> RelativelyPrime (int n) x , isProp-RelativelyPrime)
                (\ x y r -> ΣProp-path (isProp-isOfHLevel 1) (rp-eq x y r))
    where
    rp-f : (x y : ℤ) -> (x ~ y) -> RelativelyPrime (int n) x -> RelativelyPrime (int n) y
    rp-f x y (congruent-mod n%xy) rp-x d nn-d d%n d%y = rp-x d nn-d d%n d%x
      where
      d%xyy : d div ((x + (- y)) + y)
      d%xyy = div-+ (div-trans d%n n%xy) d%y
      d%x : d div x
      d%x = subst (d div_)
            (+-assoc >=>
             +-right (+-commute >=> int.add-minus-zero) >=>
             +-right-zero)
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
    unit->coprime' = SetQuotientElim.elimProp2 (\x y -> (isPropΠ (\_ -> isProp-CoprimeN {x}))) handle
      where
      handle : (x y : ℤ) -> ([ x * y ] == 1#) -> (CoprimeN [ x ])
      handle x y p d nn-d d%n d%x = divℤ-one->one nn-d d%1
        where
        c : (int 1) ~ (x * y)
        c = sym-~ (SetQuotientElim.pathRec isPropValued-~ isEquivRel-~ _ _ p)

        d%1-xy : d div ((int 1) + (- (x * y)))
        d%1-xy = div-trans d%n (CongruentMod.n%ab c)

        d%xy : d div (x * y)
        d%xy = div-*ʳ d%x y

        xy-path : ((int 1) + (- (x * y))) + (x * y) == (int 1)
        xy-path = +-assoc >=> +-right (+-commute >=> int.add-minus-zero) >=>
                  +-right-zero

        d%1 : d div (int 1)
        d%1 = subst (d div_) xy-path (div-+ d%1-xy d%xy)

    unit->coprime : (x : ℤ/nℤ n) -> (Unit x) -> (CoprimeN x)
    unit->coprime x (y , p) = unit->coprime' x y p


    lc->unit : {x : ℤ} -> LinearCombination (int n) x (int 1) -> Unit [ x ]
    lc->unit {x} lc = [ y ] , eq/ (x * y) (int 1) (congruent-mod n%xy-1)
      where
      module lc = LinearCombination lc

      y : Int
      y = lc.y

      path : (- lc.x) * (int n) == x * lc.y + (- (int 1))
      path = minus-extract-left >=>
             cong -_ (sym +-right-zero >=> +-right (sym (add-minus-zero {lc.y * x})) >=>
                      sym +-assoc >=> +-left lc.path >=> +-commute) >=>
             minus-distrib-+ >=> +-left minus-double-inverse >=>
             +-left *-commute
        where
        open int

      n%xy-1 : (int n) div (x * y + (- (int 1)))
      n%xy-1 = ∣ (- lc.x) , path ∣

    coprime->unit : (x : ℤ/nℤ n) -> (CoprimeN x) -> (Unit x)
    coprime->unit = SetQuotientElim.elimProp (\x -> (isPropΠ (\_ -> isProp-Unit {x = x}))) handle
      where
      handle : (x : ℤ) -> (RelativelyPrime (int n) x) -> (Unit [ x ])
      handle x rp = lc->unit (gcd->linear-combo (relatively-prime->gcdⁱ rp))

  module _ where
    unit'->coprime : (x : ℤ/nℤ n) -> (Unit' x) -> (CoprimeN x)
    unit'->coprime x u = unit->coprime' x u.inv u.path
      where
      module u = Unit' u


    lc->unit' : {x : ℤ} -> LinearCombination (int n) x (int 1) -> Unit' [ x ]
    lc->unit' {x} lc = unit' [ x ] [ y ] (eq/ (x * y) (int 1) (congruent-mod n%xy-1))
      where
      module lc = LinearCombination lc

      y : Int
      y = lc.y

      path : (- lc.x) * (int n) == x * lc.y + (- (int 1))
      path = minus-extract-left >=>
             cong -_ (sym +-right-zero >=> +-right (sym (add-minus-zero {lc.y * x})) >=>
                      sym +-assoc >=> +-left lc.path >=> +-commute) >=>
             minus-distrib-+ >=> +-left minus-double-inverse >=>
             +-left *-commute
        where
        open int

      n%xy-1 : (int n) div (x * y + (- (int 1)))
      n%xy-1 = ∣ (- lc.x) , path ∣

    coprime->unit' : (x : ℤ/nℤ n) -> (CoprimeN x) -> (Unit' x)
    coprime->unit' = SetQuotientElim.elimProp (\x -> (isPropΠ (\_ -> isProp-Unit'))) handle
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
