{-# OPTIONS --cubical --safe --exact-split #-}

module nat.order where

open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import nat.arithmetic
open import nat.properties
open import relation
open import sigma


_≤_ : Nat -> Nat -> Type₀
m ≤ n = Σ[ x ∈ Nat ] x +' m == n

_≥_ : Nat -> Nat -> Set
m ≥ n = n ≤ m

_<_ : Nat -> Nat -> Set
m < n = (suc m) ≤ n

_>_ : Nat -> Nat -> Set
m > n = n < m

_≮_ : Nat -> Nat -> Set
m ≮ n = ¬ (m < n)

_≯_ : Nat -> Nat -> Set
m ≯ n = ¬ (m > n)

module _ {m n : Nat} (lt1@(x1 , p1) lt2@(x2 , p2) : m ≤ n) where
  private
    p-x : x1 == x2
    p-x = (transport (sym (+'-right-path m)) (p1 >=> (sym p2)))

    p-p : PathP (\i -> p-x i +' m == n) p1 p2
    p-p = isSet->Square isSetNat

  isProp≤ : lt1 == lt2
  isProp≤  i .fst = p-x i
  isProp≤  i .snd = p-p i

isProp≮ : {m n : Nat} -> isProp (m ≮ n)
isProp≮ = isProp¬ _

zero-≤ : {n : Nat} -> zero ≤ n
zero-≤ {n} = (n , +'-right-zero)

suc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n
suc-≤ (x , p) = (x , +'-right-suc >=> cong suc p)

zero-< : {n : Nat} -> zero < (suc n)
zero-< = suc-≤ zero-≤

suc-< : {m n : Nat} -> m < n -> suc m < suc n
suc-< = suc-≤

zero-≮ : {n : Nat} -> n ≮ zero
zero-≮ (zero  , p) = zero-suc-absurd (sym p)
zero-≮ (suc _ , p) = zero-suc-absurd (sym p)

same-≤ : (n : Nat) -> n ≤ n
same-≤ zero = zero-≤
same-≤ (suc n) = suc-≤ (same-≤ n)

pred-≤ : {m n : Nat} -> m ≤ n -> pred m ≤ pred n
pred-≤ {m = zero}              _       = zero-≤
pred-≤ {m = suc _} {n = zero}  lt      = bot-elim (zero-≮ lt)
pred-≤ {m = suc _} {n = suc _} (x , p) = (x , cong pred (sym +'-right-suc >=> p))

add1-< : (n : Nat) -> n < (suc n)
add1-< zero = zero-<
add1-< (suc n) = suc-< (add1-< n)

right-suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ (suc n)
right-suc-≤ (x , p) = suc x , cong suc p

right-suc-< : {m n : Nat} -> m < n -> m < (suc n)
right-suc-< = right-suc-≤

trans-≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-≤ (x1 , p1) (x2 , p2) = x2 +' x1 , +'-assoc {x2} >=> cong (x2 +'_) p1 >=> p2

trans-<-≤ : {m n o : Nat} -> (m < n) -> (n ≤ o) -> (m < o)
trans-<-≤ = trans-≤

trans-≤-< : {m n o : Nat} -> m ≤ n -> n < o -> m < o
trans-≤-< {m} {n} {o} (x1 , p1) (x2 , p2) = x2 +' x1 , path
  where
  path : (x2 +' x1) +' suc m == o
  path = +'-assoc {x2}
         >=> cong (x2 +'_) (+'-right-suc >=> cong suc p1)
         >=> p2

trans-< : {m n o : Nat} -> (m < n) -> (n < o) -> (m < o)
trans-< lt1 lt2 = trans-≤-< (pred-≤ (right-suc-≤ lt1)) lt2

<->!= : {m n : Nat} -> m < n -> m != n
<->!= {m} {n} (x , p) m==n =
  zero-suc-absurd (transport (sym (+'-right-path m)) (m==n >=> sym p >=> +'-right-suc))

same-≮ : {n : Nat} -> (n ≮ n)
same-≮ {n} lt = <->!= lt refl

<->Pos' : {x y : Nat} -> x < y -> Pos' y
<->Pos' (zero  , p) = transport (\i -> Pos' (p i)) tt
<->Pos' (suc _ , p) = transport (\i -> Pos' (p i)) tt

-- suc-≤ introduces a path

suc-≤-iso : {m n : Nat} -> Iso (m ≤ n) (suc m ≤ suc n)
Iso.fun suc-≤-iso = suc-≤
Iso.inv suc-≤-iso = pred-≤
Iso.rightInv suc-≤-iso _ = isProp≤ _ _
Iso.leftInv  suc-≤-iso _ = isProp≤ _ _

suc-≤-== : {m n : Nat} -> (m ≤ n) == (suc m ≤ suc n)
suc-≤-== = ua (isoToEquiv suc-≤-iso)

+-left-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (x +' m) ≤ (x +' n)
+-left-≤ {m} {n} x =
  induction {P = (\x -> m ≤ n == (x +' m) ≤ (x +' n))}
            refl (_>=> suc-≤-==) x

+-right-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (m +' x) ≤ (n +' x)
+-right-≤ {m} {n} x =
  transport (\i -> m ≤ n == (+'-commute {x} {m} i) ≤ (+'-commute {x} {n} i)) (+-left-≤ x)

≤-antisym : {m n : Nat} -> m ≤ n -> n ≤ m -> m == n
≤-antisym (zero  , p1) _ = p1
≤-antisym {m} {n} (suc i , p1) (j , p2) = bot-elim (zero-suc-absurd (sym path))
  where
  path : (suc i +' j) == 0
  path = transport (sym (+'-right-path n))
                   (+'-assoc {suc i} >=> cong (suc i +'_) p2 >=> p1)

private
  ≮->≥ : {m n : Nat} -> m ≮ n -> m ≥ n
  ≮->≥             {n = zero}  m≮n = zero-≤
  ≮->≥ {m = zero}  {n = suc n} m≮n = bot-elim (m≮n zero-<)
  ≮->≥ {m = suc m} {n = suc n} m≮n = suc-≤ (≮->≥ (m≮n ∘ suc-≤))

  ≮-≥-iso : {m n : Nat} -> Iso (m ≮ n) (m ≥ n)
  Iso.fun ≮-≥-iso = ≮->≥
  Iso.inv ≮-≥-iso n≤m m<n = same-≮ (trans-≤-< n≤m m<n)
  Iso.rightInv ≮-≥-iso _ = isProp≤ _ _
  Iso.leftInv  ≮-≥-iso _ = isProp≮ _ _

≮==≥ : {m n : Nat} -> m ≮ n == m ≥ n
≮==≥ = ua (isoToEquiv ≮-≥-iso)

-- Properties of ≤/< and -'

≤-minus : {m n p : Nat} -> (m +' n) ≤ p -> m ≤ (p -' n)
≤-minus {m} {n} {p} (i , path) = (i , path')
  where
  path' : i +' m == p -' n
  path' =
    sym (+'-minus-right n)
    >=> (cong (_-' n) (+'-assoc {i} >=> path))

<-minus : {m n p : Nat} -> (m +' n) < p -> m < (p -' n)
<-minus {m} {n} {p} (i , path) = (i , path')
  where
  path' : i +' (suc m) == p -' n
  path' =
    sym (+'-minus-right n)
    >=> (cong (_-' n) (+'-assoc {i} >=> path))

<-minus-rev : {m n p : Nat} -> m < (p -' n) -> (m +' n) < p
<-minus-rev {m} {n} {p} m<p-n@(i , path) = (i , path')
  where
  check-path : i +' suc m == p -' n
  check-path = path
  path' : i +' (suc (m +' n)) == p
  path' =
    sym (+'-assoc {i} {suc m} {n})
    >=> (cong (_+' n) path)
    >=> (+'-minus-rev n (<->Pos' m<p-n))

<-minus-iso : {m n p : Nat} -> Iso ((m +' n) < p) (m < (p -' n))
Iso.fun <-minus-iso = <-minus
Iso.inv <-minus-iso = <-minus-rev
Iso.rightInv <-minus-iso _ = ΣProp-path (isSetNat _ _) refl
Iso.leftInv  <-minus-iso _ = ΣProp-path (isSetNat _ _) refl

<-minus-path : {m n p : Nat} -> ((m +' n) < p) == (m < (p -' n))
<-minus-path = ua (isoToEquiv <-minus-iso)

-- Flipped ≤
_≤'_ : Nat -> Nat -> Type₀
m ≤' n = Σ[ x ∈ Nat ] m +' x == n

≤==≤' : {m n : Nat} -> m ≤ n == m ≤' n
≤==≤' {m} {n} i = Σ[ x ∈ Nat ] ((+'-commute {x} {m} i) == n)

≤'->≤ : {m n : Nat} -> m ≤' n -> m ≤ n
≤'->≤ = transport (sym ≤==≤')

-- Step based ≤
data _≤s_ : Nat -> Nat -> Set where
 refl-≤s : {m : Nat} -> m ≤s m
 step-≤s : {m n : Nat} -> m ≤s n -> m ≤s suc n

_<s_ : Nat -> Nat -> Set
m <s n = (suc m) ≤s n

suc-≤s : {m n : Nat} -> m ≤s n -> (suc m) ≤s (suc n)
suc-≤s refl-≤s = refl-≤s
suc-≤s (step-≤s rec) = step-≤s (suc-≤s rec)

zero-≤s : (m : Nat) -> 0 ≤s m
zero-≤s zero = refl-≤s
zero-≤s (suc n) = step-≤s (zero-≤s n)

≤s->≤ : {m n : Nat} -> m ≤s n -> m ≤ n
≤s->≤ {m} refl-≤s = same-≤ m
≤s->≤ (step-≤s rec) = right-suc-≤ (≤s->≤ rec)

≤->≤s : {m n : Nat} -> m ≤ n -> m ≤s n
≤->≤s {m} {n}     (zero , p) = transport (\i -> m ≤s (p i)) refl-≤s
≤->≤s {n = zero}  (suc i , p) = zero-suc-absurd (sym p)
≤->≤s {n = suc _} (suc i , p) = step-≤s (≤->≤s (i , cong pred p))

-- Decidable <
decide-nat< : (x : Nat) -> (y : Nat) -> Dec (x < y)
decide-nat< _       zero    = no zero-≮
decide-nat< zero    (suc n) = yes zero-<
decide-nat< (suc m) (suc n) with (decide-nat< m n)
... | yes pr = yes (suc-≤ pr)
... | no f = no (f ∘ pred-≤)


module _ where
  private
    module _ {P : Nat -> Set}
             (p0 : P zero)
             (psuc : {m : Nat} -> ({n : Nat} -> (n ≤s m) -> P n) -> P (suc m))
             where
      InnerP : Nat -> Type₀
      InnerP m = ({n : Nat} -> (n ≤s m) -> P n)

      inner-zero : InnerP 0
      inner-zero refl-≤s = p0

      inner-suc : {n : Nat} -> InnerP n -> InnerP (suc n)
      inner-suc f refl-≤s      = psuc f
      inner-suc f (step-≤s lt) = f lt

      inner : (m : Nat) -> InnerP m
      inner zero    = inner-zero
      inner (suc m) = inner-suc (inner m)

      strong-induction-≤s : (m : Nat) -> P m
      strong-induction-≤s m = inner m refl-≤s

  strong-induction : {P : Nat -> Set}
                     (p0 : P zero)
                     (psuc : {m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m))
                     -> (m : Nat) -> P m
  strong-induction p0 psuc m = strong-induction-≤s p0 (\f -> psuc (f ∘ ≤->≤s)) m

  strong-induction' : {P : Nat -> Set}
                     (p : {m : Nat} -> ({n : Nat} -> (n < m) -> P n) -> P m)
                     -> (m : Nat) -> P m
  strong-induction' {P} p m = strong-induction-≤s p0 (\f -> p (f ∘ ≤->≤s ∘ pred-≤)) m
    where
    p0 : P 0
    p0 = p (bot-elim ∘ zero-≮)


-- Induction based ≤
data _≤i_ : Nat -> Nat -> Set where
 zero-≤i : {n : Nat} -> zero ≤i n
 suc-≤i : {m n : Nat} -> m ≤i n -> suc m ≤i suc n

_<i_ : Nat -> Nat -> Set
m <i n = (suc m) ≤i n

isProp≤i : {m n : Nat} -> isProp (m ≤i n)
isProp≤i zero-≤i      zero-≤i      = refl
isProp≤i (suc-≤i lt1) (suc-≤i lt2) = cong suc-≤i (isProp≤i lt1 lt2)

zero-<i : {n : Nat} -> zero <i (suc n)
zero-<i = suc-≤i zero-≤i

same-≤i : (n : Nat) -> n ≤i n
same-≤i zero    = zero-≤i
same-≤i (suc n) = suc-≤i (same-≤i n)

right-suc-≤i : {m n : Nat} -> m ≤i n -> m ≤i (suc n)
right-suc-≤i zero-≤i = zero-≤i
right-suc-≤i (suc-≤i lt) = suc-≤i (right-suc-≤i lt)

pred-≤i : {m n : Nat} -> m ≤i n -> pred m ≤i pred n
pred-≤i zero-≤i     = zero-≤i
pred-≤i (suc-≤i lt) = lt

≤->≤i : {m n : Nat} -> m ≤ n -> m ≤i n
≤->≤i {m = m}     (0     , p) = transport (\i -> m ≤i p i) (same-≤i m)
≤->≤i {n = zero}  (suc i , p) = bot-elim (zero-suc-absurd (sym p))
≤->≤i {n = suc n} (suc i , p) = right-suc-≤i (≤->≤i (i , cong pred p))

≤i->≤ : {m n : Nat} -> m ≤i n -> m ≤ n
≤i->≤ zero-≤i = zero-≤
≤i->≤ (suc-≤i lt) = suc-≤ (≤i->≤ lt)


≤-≤i-iso : {m n : Nat} -> Iso (m ≤ n) (m ≤i n)
Iso.fun ≤-≤i-iso = ≤->≤i
Iso.inv ≤-≤i-iso = ≤i->≤
Iso.rightInv ≤-≤i-iso _ = isProp≤i _ _
Iso.leftInv  ≤-≤i-iso _ = isProp≤ _ _

≤==≤i : {m n : Nat} -> (m ≤ n) == (m ≤i n)
≤==≤i = ua (isoToEquiv ≤-≤i-iso)
