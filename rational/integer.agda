{-# OPTIONS --cubical --safe --exact-split #-}

module rational.integer where

open import abs
open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.int
open import base
open import equality
open import fin
open import functions
open import hlevel
open import int
open import nat
open import nat.order
open import quotient-remainder-int
open import rational
open import ring
open import ring.implementations.int
open import semiring
open import semiring.instances.nat
open import set-quotient
open import sigma.base

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
  quotientℤ n (int.pos d , _) = quotient n (suc d , tt)
  quotientℤ n (int.neg d , _) = (quotient (- n) (suc d , tt))
  quotientℤ n (int.zero-int , (inj-l ()))
  quotientℤ n (int.zero-int , (inj-r ()))

  remainderℤ : (n : ℤ) (d : ℤ*) -> ℤ
  remainderℤ n (int.pos d , _) = int (Fin.i (remainder n (suc d , tt)))
  remainderℤ n (int.neg d , _) = - (int (Fin.i (remainder (- n) (suc d , tt))))
  remainderℤ n (int.zero-int , (inj-l ()))
  remainderℤ n (int.zero-int , (inj-r ()))


  ℤ*-* : ℤ* -> ℤ* -> ℤ*
  ℤ*-* (m , nz-m) (d , nz-d) = (m * d , int.*-NonZero-NonZero nz-m nz-d)

  quotientℤ-path : (a : ℤ) (d : ℤ*) -> (quotientℤ a d * ⟨ d ⟩) + (remainderℤ a d) == a
  quotientℤ-path a (int.pos d , _) =
    QuotientRemainder.path (quotient-remainder (suc d , tt) a)
  quotientℤ-path a (int.neg d , _) =
    +-left minus-extract-right >=>
    sym int.minus-distrib-+ >=>
    cong -_ (QuotientRemainder.path (quotient-remainder (suc d , tt) (- a))) >=>
    minus-double-inverse
  quotientℤ-path a (int.zero-int , inj-l ())
  quotientℤ-path a (int.zero-int , inj-r ())

  quotientℤ-multiple-path :
    (m : ℤ*) -> (n : ℤ) -> (d : ℤ*) ->
    quotientℤ n d == quotientℤ (⟨ m ⟩ * n) (ℤ*-* m d)
  quotientℤ-multiple-path m@(int.pos m' , _) n d@(int.pos d' , _) =
    quotient-multiple-path (suc m' , tt) n (suc d' , tt) >=>
    cong (quotientℤ (int.pos m' * n)) (ΣProp-path {x = _ , (inj-l tt)} int.isPropNonZero int-inject-*')
  quotientℤ-multiple-path m@(int.pos m' , _) n d@(int.neg d' , _) =
    quotient-multiple-path (suc m' , tt) (- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) minus-extract-right >=>
    cong (quotientℤ (int.pos m' * n)) (ΣProp-path {x = _ , (inj-r tt)} int.isPropNonZero p1)
    where
    p1 : (int.neg (d' + (m' * suc d'))) == (int.pos m' * int.neg d')
    p1 = cong -_ int-inject-*' >=> sym minus-extract-right
  quotientℤ-multiple-path m@(int.neg m' , _) n d@(int.pos d' , _) =
    -- TODO
    cong (\x -> quotient x (suc d' , tt)) (sym (int.ℤminus-double-inverse {n})) >=>
    quotient-multiple-path (suc m' , tt) (- (- n)) (suc d' , tt) >=>
    cong (\x -> quotient x ((suc m' , tt) *⁺ (suc d' , tt))) p2 >=>
    cong (quotientℤ (int.neg m' * n)) (ΣProp-path {x = _ , (inj-r tt)} int.isPropNonZero p1)
    where
    p1 : int.neg (d' + (m' * suc d')) == (int.neg m' * int.pos d')
    p1 = cong -_ int-inject-*' >=> sym minus-extract-left
    p2 : int.pos m' * (- (- n)) == - (int.neg m' * n)
    p2 = minus-extract-right >=> sym minus-extract-left >=> minus-extract-right
  quotientℤ-multiple-path m@(int.neg m' , _) n d@(int.neg d' , _) =
    quotient-multiple-path (suc m' , tt) (- n) (suc d' , tt) >=>
    cong (\x -> quotient x _) (minus-extract-right >=> sym minus-extract-left) >=>
    cong (quotientℤ (int.neg m' * n)) (ΣProp-path {x = _ , (inj-l tt)} int.isPropNonZero p1)
    where
    p1 : int (suc m' * suc d') == (int.neg m' * int.neg d')
    p1 = int-inject-*' >=> sym minus-double-inverse >=>
         cong -_ (sym minus-extract-right) >=>
         sym minus-extract-left
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
    int.minus-NonNeg {remainderℤ (- n) (int.pos d' , inj-l tt)}
                     (remainderℤ-NonNeg (- n) (int.pos d' , inj-l tt) _)

private
  floor' : ℚ' -> ℤ
  floor' r = quotientℤ (numer r) (denom r , rNonZero r)

  opaque
    floor'-r~ : (x y : ℚ') -> (x r~ y) -> floor' x == floor' y
    floor'-r~ x y r =
      quotientℤ-multiple-path dy* nx dx* >=>
      cong2 quotientℤ n-path (ΣProp-path int.isPropNonZero d-path)
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
      ; NonZero-denominator = isProp->PathPᵉ (\i -> int.isPropNonZero {dp i}) (rNonZero q') (rNonZero q) i
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
        +-right (sym (int.add-minus-zero {((quotientℤ na da*) * da)})) >=>
        sym +-assoc >=>
        +-left (+-commute >=> quotientℤ-path na da*)

      r-path-b : (remainderℤ nb db*) == nb + (- ((quotientℤ nb db*) * db))
      r-path-b =
        sym +-right-zero >=>
        +-right (sym (int.add-minus-zero {((quotientℤ nb db*) * db)})) >=>
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
  unfolding ℚ

  floor : ℚ -> ℤ
  floor = SetQuotientElim.rec int.isSetInt floor' floor'-r~

  floorℚ : ℚ -> ℚ
  floorℚ = ℤ->ℚ ∘ floor

  fractional-part : ℚ -> ℚ
  fractional-part = SetQuotientElim.rec isSetℚ
                      (\a -> [ fractional-part' a ])
                      (\a b r -> eq/ _ _ (fractional-part'-preserves-r~ a b r))

opaque
  unfolding _r+_ floor

  fractional-part-r+ : (q : ℚ) -> floorℚ q r+ (fractional-part q) == q
  fractional-part-r+ = SetQuotientElim.elimProp (\_ -> (isSetℚ _ _))
                        (\q -> cong [_] (fractional-part'-r+' q))


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
