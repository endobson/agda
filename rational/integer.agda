{-# OPTIONS --cubical --safe --exact-split #-}

module rational.integer where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality
open import fin
open import fraction.order
open import fraction.sign
open import functions
open import hlevel
open import int
open import int.base
open import int.cover
open import int.nat
open import int.order
open import int.sign
open import nat
open import nat.order
open import order
open import order.instances.int
open import ordered-additive-group
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.instances.int
open import quotient-remainder-int
open import rational
open import rational.order
open import ring
open import ring.implementations.int
open import semiring
open import semiring.instances.nat
open import set-quotient
open import sigma.base

import sign

private
  numer : ℚ' -> ℤ
  numer = ℚ'.numerator
  denom : ℚ' -> ℤ
  denom = ℚ'.denominator
  rNonZero : (r : ℚ') -> NonZero (denom r)
  rNonZero = ℚ'.NonZero-denominator

-- Floor
private
  ℤ* = Σ ℤ NonZero

  quotientℤ : (n : ℤ) (d : ℤ*) -> ℤ
  quotientℤ n (pos d , _) = quotient n (suc d , tt)
  quotientℤ n (neg d , _) = (quotient (- n) (suc d , tt))
  quotientℤ n (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)

  remainderℤ : (n : ℤ) (d : ℤ*) -> ℤ
  remainderℤ n (pos d , _) = int (Fin.i (remainder n (suc d , tt)))
  remainderℤ n (neg d , _) = - (int (Fin.i (remainder (- n) (suc d , tt))))
  remainderℤ n (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)

  small-remainderℤ-Pos : (n : ℤ) (d : ℤ*) -> Pos ⟨ d ⟩ -> remainderℤ n d < ⟨ d ⟩
  small-remainderℤ-Pos n (pos d , _) _ =
    ℕ->ℤ-preserves-< (Fin.i<n (remainder n (suc d , tt)))
  small-remainderℤ-Pos n (neg d , _) 0<d = bot-elim (asym-< neg<0 0<d)
  small-remainderℤ-Pos n (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)

  small-remainderℤ-Neg : (n : ℤ) (d : ℤ*) -> Neg ⟨ d ⟩ -> ⟨ d ⟩ < remainderℤ n d
  small-remainderℤ-Neg n d*@(neg d , _) _ =
    minus-flips-< (ℕ->ℤ-preserves-< (Fin.i<n (remainder (- n) (suc d , tt))))
  small-remainderℤ-Neg n (pos d , _) d<0 = bot-elim (asym-< 0<pos d<0)
  small-remainderℤ-Neg n (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)

  ℤ*-* : ℤ* -> ℤ* -> ℤ*
  ℤ*-* (m , nz-m) (d , nz-d) = (m * d , *-NonZero-NonZero nz-m nz-d)

  quotientℤ-path : (a : ℤ) (d : ℤ*) -> (quotientℤ a d * ⟨ d ⟩) + (remainderℤ a d) == a
  quotientℤ-path a (pos d , _) =
    QuotientRemainder.path (quotient-remainder (suc d , tt) a)
  quotientℤ-path a (neg d , _) =
    +-left minus-extract-right >=>
    sym minus-distrib-plus >=>
    cong -_ (QuotientRemainder.path (quotient-remainder (suc d , tt) (- a))) >=>
    minus-double-inverse
  quotientℤ-path a (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)

  quotientℤ-multiple-path :
    (m : ℤ*) -> (n : ℤ) -> (d : ℤ*) ->
    quotientℤ n d == quotientℤ (⟨ m ⟩ * n) (ℤ*-* m d)
  quotientℤ-multiple-path m@(pos m' , _) n d@(pos d' , _) =
    quotient-multiple-path (suc m' , tt) n (suc d' , tt) >=>
    cong (quotientℤ (pos m' * n)) (ΣProp-path {x = _ , (inj-l 0<pos)} isPropNonZero ℕ->ℤ-*)
  quotientℤ-multiple-path m@(pos m' , _) n d@(neg d' , _) =
    quotient-multiple-path (suc m' , tt) (- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) minus-extract-right >=>
    cong (quotientℤ (pos m' * n)) (ΣProp-path {x = _ , (inj-r neg<0)} isPropNonZero p1)
    where
    p1 : (neg (d' + (m' * suc d'))) == (pos m' * neg d')
    p1 = cong -_ ℕ->ℤ-* >=> sym minus-extract-right
  quotientℤ-multiple-path m@(neg m' , _) n d@(pos d' , _) =
    -- TODO
    cong (\x -> quotient x (suc d' , tt)) p3 >=>
    quotient-multiple-path (suc m' , tt) (- (- n)) (suc d' , tt) >=>
    cong (\x -> quotient x ((suc m' , tt) *⁺ (suc d' , tt))) p2 >=>
    cong (quotientℤ (neg m' * n)) (ΣProp-path {x = _ , (inj-r neg<0)} isPropNonZero p1)
    where
    p1 : neg (d' + (m' * suc d')) == (neg m' * pos d')
    p1 = cong -_ ℕ->ℤ-* >=> sym minus-extract-left
    p2 : pos m' * (- (- n)) == - (neg m' * n)
    p2 = minus-extract-right >=> sym minus-extract-left >=> minus-extract-right
    p3 : n == (- (- n))
    p3 = sym minus-double-inverse
  quotientℤ-multiple-path m@(neg m' , _) n d@(neg d' , _) =
    quotient-multiple-path (suc m' , tt) (- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) (minus-extract-right >=> sym minus-extract-left) >=>
    cong (quotientℤ (neg m' * n)) (ΣProp-path {x = _ , (inj-l 0<pos)} isPropNonZero p1)
    where
    p1 : int (suc m' * suc d') == (neg m' * neg d')
    p1 = ℕ->ℤ-* >=> sym minus-double-inverse >=>
         cong -_ (sym minus-extract-right) >=>
         sym minus-extract-left
  quotientℤ-multiple-path (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)
  quotientℤ-multiple-path (pos _ , _) _ (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)
  quotientℤ-multiple-path (neg _ , _) _ (zero-int , nz) = bot-elim (NonZero->!=0 nz refl)


  remainderℤ-NonNeg : (n : ℤ) (d : ℤ*) -> Pos ⟨ d ⟩ -> NonNeg (remainderℤ n d)
  remainderℤ-NonNeg n (pos _ , _) _ = 0≤nonneg
  remainderℤ-NonNeg n (neg _ , _) 0<d = bot-elim (asym-< 0<d neg<0)
  remainderℤ-NonNeg n (zero-int , _) 0<0 = bot-elim (irrefl-< 0<0)

  remainderℤ-NonPos : (n : ℤ) (d : ℤ*) -> Neg ⟨ d ⟩ -> NonPos (remainderℤ n d)
  remainderℤ-NonPos n (neg d' , _) _ =
    minus-flips-0≤ (remainderℤ-NonNeg (- n) (pos d' , inj-l 0<pos) 0<pos)
  remainderℤ-NonPos n (nonneg d' , _) d<0 =
    bot-elim (convert-≤ 0≤nonneg d<0)

private
  floor' : ℚ' -> ℤ
  floor' r = quotientℤ (numer r) (denom r , rNonZero r)

  opaque
    floor'-r~ : (x y : ℚ') -> (x r~ y) -> floor' x == floor' y
    floor'-r~ x y r =
      quotientℤ-multiple-path dy* nx dx* >=>
      cong2 quotientℤ n-path (ΣProp-path isPropNonZero d-path)
      >=> sym (quotientℤ-multiple-path dx* ny dy*)

      where
      nx ny dx dy : ℤ
      nx = numer x
      ny = numer y
      dx = denom x
      dy = denom y
      dx* : ℤ*
      dx* = denom x , rNonZero x
      dy* : ℤ*
      dy* = denom y , rNonZero y

      n-path : dy * nx == dx * ny
      n-path = *-commute >=> r >=> *-commute

      d-path : dy * dx == dx * dy
      d-path = *-commute

  fractional-part' : ℚ' -> ℚ'
  fractional-part' r = record
    { numerator = (remainderℤ (numer r) (denom r , rNonZero r))
    ; denominator = (denom r)
    ; NonZero-denominator = (rNonZero r)
    }

  opaque
    fractional-part'-r+' : (q : ℚ') -> ℤ->ℚ' (floor' q) r+' (fractional-part' q) == q
    fractional-part'-r+' q = (\i -> record
      { numerator = np i
      ; denominator = dp i
      ; NonZero-denominator = isProp->PathPᵉ (\i -> isPropNonZero {dp i}) (rNonZero q') (rNonZero q) i
      })
      where
      q' : ℚ'
      q' = ℤ->ℚ' (floor' q) r+' (fractional-part' q)

      np : numer q' == numer q
      np = cong numer (r+'-eval {ℤ->ℚ' (floor' q)} {fractional-part' q}) >=>
           +-right *-right-one >=>
           quotientℤ-path (numer q) (denom q , rNonZero q)
      dp : denom q' == denom q
      dp = cong denom (r+'-eval {ℤ->ℚ' (floor' q)} {fractional-part' q}) >=>
           *-left-one

    fractional-part'-preserves-r~ : (a b : ℚ') -> (a r~ b) ->
                                    (fractional-part' a r~ fractional-part' b)
    fractional-part'-preserves-r~ a b r = ans
      where
      na nb da db : ℤ
      na = numer a
      nb = numer b
      da = denom a
      db = denom b
      da* : ℤ*
      da* = (da , rNonZero a)
      db* : ℤ*
      db* = (db , rNonZero b)

      r-path-a : (remainderℤ na da*) == na + (- ((quotientℤ na da*) * da))
      r-path-a =
        sym +-right-zero >=>
        +-right (sym +-inverse) >=>
        sym +-assoc >=>
        +-left (+-commute >=> quotientℤ-path na da*)

      r-path-b : (remainderℤ nb db*) == nb + (- ((quotientℤ nb db*) * db))
      r-path-b =
        sym +-right-zero >=>
        +-right (sym +-inverse) >=>
        sym +-assoc >=>
        +-left (+-commute >=> quotientℤ-path nb db*)

      inner-path : (((quotientℤ na da*) * da) * db) ==
                    (((quotientℤ nb db*) * db) * da)
      inner-path = *-assoc >=> cong2 _*_ (floor'-r~ a b r) *-commute >=> sym *-assoc

      mid-path : (na + (- ((quotientℤ na da*) * da))) * db ==
                 (nb + (- ((quotientℤ nb db*) * db))) * da
      mid-path =
        *-distrib-+-right >=>
        (cong2 _+_ r (minus-extract-left >=> (cong -_ inner-path) >=>
                          sym minus-extract-left)) >=>
        (sym *-distrib-+-right)

      ans : (remainderℤ na da*) * db == (remainderℤ nb db*) * da
      ans = *-left r-path-a >=> mid-path >=> *-left (sym r-path-b)

  opaque
    NonNeg-fractional-part' : (q : ℚ') -> sign.NonNeg (fractional-part' q)
    NonNeg-fractional-part' q = case (rNonZero q) of
      \{ (inj-l pd) -> NonNeg-nd->ℚ' (*-preserves-0≤
           (remainderℤ-NonNeg (numer q) (denom q , rNonZero q) pd)
           (weaken-< pd))
       ; (inj-r nd) -> NonNeg-nd->ℚ' (*-flips-≤0
           (remainderℤ-NonPos (numer q) (denom q , rNonZero q) nd)
           (weaken-< nd))
       }

    fractional-part'<1 : (q : ℚ') -> fractional-part' q ℚ'< (ℕ->ℚ' 1)
    fractional-part'<1 q = case (rNonZero q) of
      \{ (inj-l pd) -> ℚ'<1-Pos-denominator (fractional-part' q) pd
                         (small-remainderℤ-Pos _ _ pd)
       ; (inj-r nd) -> ℚ'<1-Neg-denominator (fractional-part' q) nd
                         (small-remainderℤ-Neg _ _ nd)
       }


opaque
  unfolding ℚ

  floor : ℚ -> ℤ
  floor = SetQuotientElim.rec isSetInt floor' floor'-r~

  floorℚ : ℚ -> ℚ
  floorℚ = ℤ->ℚ ∘ floor

  fractional-part : ℚ -> ℚ
  fractional-part = SetQuotientElim.rec isSetℚ
                      (\a -> [ fractional-part' a ])
                      (\a b r -> eq/ _ _ (fractional-part'-preserves-r~ a b r))

opaque
  unfolding _r+_ floor ℚ<-raw

  fractional-part-r+ : (q : ℚ) -> floorℚ q r+ (fractional-part q) == q
  fractional-part-r+ = SetQuotientElim.elimProp (\_ -> (isSetℚ _ _))
                        (\q -> cong [_] (fractional-part'-r+' q))

  0≤fractional-part : (q : ℚ) -> 0# ≤ fractional-part q
  0≤fractional-part q = NonNeg-0≤ (fractional-part q) (NonNeg-fractional-part q)
    where
    NonNeg-fractional-part : (q : ℚ) -> sign.NonNeg (fractional-part q)
    NonNeg-fractional-part =
      SetQuotientElim.elimProp (\q -> sign.isProp-NonNeg (fractional-part q))
      (\q -> NonNeg-ℚ'->ℚ (NonNeg-fractional-part' q))

  fractional-part<1 : (q : ℚ) -> fractional-part q < 1#
  fractional-part<1 =
    SetQuotientElim.elimProp (\q -> isProp-<)
      (\q -> ℚ<-cons (fractional-part'<1 q))

  ℤ->ℚ-floor : (x : ℤ) -> floor (ℤ->ℚ x) == x
  ℤ->ℚ-floor x = cong QuotientRemainder.q (snd isContr-QuotientRemainder qr)
    where
    qr : QuotientRemainder 1⁺ x
    qr = record
      { q = x
      ; r = (0 , (zero-<))
      ; path = +-right-zero >=> *-right-one
      }

  isInjective-ℤ->ℚ : isInjective ℤ->ℚ
  isInjective-ℤ->ℚ p = sym (ℤ->ℚ-floor _) >=> cong floor p >=> (ℤ->ℚ-floor _)
