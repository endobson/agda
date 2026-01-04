{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module nat.order where

open import additive-group.instances.nat
open import base
open import decision
open import equality
open import functions
open import hlevel
open import isomorphism
open import nat.arithmetic
open import nat.properties
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import relation
open import semiring.exponentiation
open import semiring.instances.nat
open import sigma.base
open import sum
open import truncation
open import univalence

open import nat.order.base public

_<⁺_ : Nat⁺ -> Nat⁺ -> Set
m <⁺ n = ⟨ m ⟩ < ⟨ n ⟩

_≤⁺_ : Nat⁺ -> Nat⁺ -> Set
m ≤⁺ n = ⟨ m ⟩ ≤ ⟨ n ⟩

suc-< : {m n : Nat} -> m < n -> suc m < suc n
suc-< = suc-≤

-- Helper constructors and paths

zero-≤->zero : {n : Nat} -> n ≤ zero -> n == zero
zero-≤->zero (0     , path) = path
zero-≤->zero (suc _ , path) = bot-elim (zero-suc-absurd (sym path))

same-pred-≤ : (n : Nat) -> pred n ≤ n
same-pred-≤ zero    = refl-≤
same-pred-≤ (suc n) = 1 , refl

same-pred-< : (n : Nat⁺) -> pred ⟨ n ⟩ < ⟨ n ⟩
same-pred-< (suc n , _) = 0 , refl

pos-pred-≤ : {m n : Nat} -> Pos' n -> m ≤ (pred n) -> m < n
pos-pred-≤ {m} {zero} ()
pos-pred-≤ {m} {suc n} _ lt = suc-≤ lt

pred-==-≤ : {m n : Nat} -> m == pred n -> m ≤ n
pred-==-≤ {n = zero}    p = (0 , p)
pred-==-≤ {n = (suc n)} p = (1 , cong suc p)

add1-< : (n : Nat) -> n < (suc n)
add1-< zero = zero-<
add1-< (suc n) = suc-< (add1-< n)

right-suc-< : {m n : Nat} -> m < n -> m < (suc n)
right-suc-< = right-suc-≤

strengthen-≤ : {m n : Nat} -> m ≤ n -> m != n -> m < n
strengthen-≤ (0     , path) ¬path = bot-elim (¬path path)
strengthen-≤ (suc x , path) ¬path = (x , +'-right-suc >=> path)

<->Pos' : {x y : Nat} -> x < y -> Pos' y
<->Pos' (zero  , p) = transport (\i -> Pos' (p i)) tt
<->Pos' (suc _ , p) = transport (\i -> Pos' (p i)) tt

Pos'->< : {y : Nat} -> Pos' y -> 0 < y
Pos'->< {zero} ()
Pos'->< {suc _} _ = zero-<

-- suc-≤ introduces a path

suc-≤-iso : {m n : Nat} -> Iso (m ≤ n) (suc m ≤ suc n)
Iso.fun suc-≤-iso = suc-≤
Iso.inv suc-≤-iso = pred-≤
Iso.rightInv suc-≤-iso _ = isProp-ℕ≤ _ _
Iso.leftInv  suc-≤-iso _ = isProp-ℕ≤ _ _

suc-≤-== : {m n : Nat} -> (m ≤ n) == (suc m ≤ suc n)
suc-≤-== = ua (isoToEquiv suc-≤-iso)

-- Helpers for exponentiation and ≤

^-suc-≤ : {m : Nat} -> m ≥ 1 -> (n : Nat) ->  (m ^ℕ n) ≤ (m ^ℕ (suc n))
^-suc-≤     (x , path) zero    = (x , path >=> (sym ^ℕ-one))
^-suc-≤ {m} m≥1        (suc n) = *₁-preserves-≤ (trans-≤ zero-≤ m≥1) (^-suc-≤ m≥1 n)

^-suc-< : {m : Nat} -> m > 1 -> (n : Nat) ->  (m ^ℕ n) < (m ^ℕ (suc n))
^-suc-<     (x , path) zero    = (x , path >=> (sym ^ℕ-one))
^-suc-< {m} m>1        (suc n) = *₁-preserves-< (weaken-< m>1) (^-suc-< m>1 n)

private
  2^n-large' : (n m : Nat) -> n == m -> n < (2 ^ℕ n)
  2^n-large' zero _ _ = zero-<
  2^n-large' (suc zero) _ _ = suc-< zero-<
  2^n-large' (suc n@(suc n')) zero p = zero-suc-absurd (sym p)
  2^n-large' (suc n@(suc n')) (suc m) p = trans-≤-< lt1 lt2
    where
    lt1 : (suc n) ≤ (2 *' n)
    lt1 = n' , +'-right-suc >=> +'-right {suc n'} (sym *'-left-one)
    lt2 : (2 *' n) < (2 ^ℕ (suc n))
    lt2 = *₁-preserves-< (zero-< {1}) (2^n-large' n m (cong pred p))


2^n-large : (n : Nat) -> n < (2 ^ℕ n)
2^n-large n = 2^n-large' n n refl


private
  ≮->≥ : {m n : Nat} -> m ≮ n -> m ≥ n
  ≮->≥             {n = zero}  m≮n = zero-≤
  ≮->≥ {m = zero}  {n = suc n} m≮n = bot-elim (m≮n zero-<)
  ≮->≥ {m = suc m} {n = suc n} m≮n = suc-≤ (≮->≥ (m≮n ∘ suc-≤))

  ≮-≥-iso : {m n : Nat} -> Iso (m ≮ n) (m ≥ n)
  Iso.fun ≮-≥-iso = ≮->≥
  Iso.inv ≮-≥-iso n≤m m<n = irrefl-< (trans-≤-< n≤m m<n)
  Iso.rightInv ≮-≥-iso _ = isProp-ℕ≤ _ _
  Iso.leftInv  ≮-≥-iso _ = isProp¬ _ _



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

≤-minus->zero : {m n : Nat} -> m ≤ n -> m -' n == 0
≤-minus->zero {zero} {zero}  lt = refl
≤-minus->zero {zero} {suc n} lt = refl
≤-minus->zero {suc m} {zero} lt = bot-elim (zero-≮ lt)
≤-minus->zero {suc m} {suc n} lt = ≤-minus->zero {m} {n} (pred-≤ lt)

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
≤s->≤ {m} refl-≤s = refl-≤
≤s->≤ (step-≤s rec) = right-suc-≤ (≤s->≤ rec)

≤->≤s : {m n : Nat} -> m ≤ n -> m ≤s n
≤->≤s {m} {n}     (zero , p) = transport (\i -> m ≤s (p i)) refl-≤s
≤->≤s {n = zero}  (suc i , p) = zero-suc-absurd (sym p)
≤->≤s {n = suc _} (suc i , p) = step-≤s (≤->≤s (i , cong pred p))

-- Decidable <

decide-nat≤ : (x : Nat) -> (y : Nat) -> Dec (x ≤ y)
decide-nat≤ zero    _       = yes zero-≤
decide-nat≤ (suc m) zero    = no zero-≮
decide-nat≤ (suc m) (suc n) with (decide-nat≤ m n)
... | yes pr = yes (suc-≤ pr)
... | no f = no (f ∘ pred-≤)

total-order-≤ : TotalOrder _≤_
total-order-≤ = (trans-≤ , connex-≤ , antisym-≤)
total-order-≥ : TotalOrder _≥_
total-order-≥ = flip-total-order total-order-≤

module _ where
  private
    module _ {ℓ : Level} {P : Nat -> Type ℓ}
             (p0 : P zero)
             (psuc : {m : Nat} -> ({n : Nat} -> (n ≤s m) -> P n) -> P (suc m))
             where
      InnerP : Nat -> Type ℓ
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

  strong-induction : {ℓ : Level} {P : Nat -> Type ℓ}
                     (p0 : P zero)
                     (psuc : {m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m))
                     -> (m : Nat) -> P m
  strong-induction p0 psuc m = strong-induction-≤s p0 (\f -> psuc (f ∘ ≤->≤s)) m

  strong-induction' : {ℓ : Level} {P : Nat -> Type ℓ}
                      (p : {m : Nat} -> ({n : Nat} -> (n < m) -> P n) -> P m)
                      -> (m : Nat) -> P m
  strong-induction' {P = P} p m = strong-induction-≤s p0 (\f -> p (f ∘ ≤->≤s ∘ pred-≤)) m
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

zero-≮i : {n : Nat} -> ¬ (n <i zero)
zero-≮i ()

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
Iso.leftInv  ≤-≤i-iso _ = isProp-ℕ≤ _ _

≤==≤i : {m n : Nat} -> (m ≤ n) == (m ≤i n)
≤==≤i = ua (isoToEquiv ≤-≤i-iso)

-- Decision procedures
decide-nat<i : (x : Nat) -> (y : Nat) -> Dec (x <i y)
decide-nat<i _       zero    = no zero-≮i
decide-nat<i zero    (suc n) = yes zero-<i
decide-nat<i (suc m) (suc n) with (decide-nat<i m n)
... | yes pr = yes (suc-≤i pr)
... | no f = no (f ∘ pred-≤i)

split-nat<i : (x : Nat) -> (y : Nat) -> (x <i y) ⊎ (y ≤i x)
split-nat<i _       zero    = inj-r zero-≤i
split-nat<i zero    (suc n) = inj-l zero-<i
split-nat<i (suc m) (suc n) with (split-nat<i m n)
... | inj-l lt = inj-l (suc-≤i lt)
... | inj-r lt = inj-r (suc-≤i lt)

-- + helpers
+-left-≤i⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) ≤i (x +' n) -> m ≤i n
+-left-≤i⁻ zero    lt = lt
+-left-≤i⁻ (suc x) lt = +-left-≤i⁻ x (pred-≤i lt)

+-left-≤i⁺ : {m n : Nat} -> (x : Nat) -> m ≤i n -> (x +' m) ≤i (x +' n)
+-left-≤i⁺ zero    lt = lt
+-left-≤i⁺ (suc x) lt = suc-≤i (+-left-≤i⁺ x lt)

+-left-<i⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) <i (x +' n) -> m <i n
+-left-<i⁻ zero    lt = lt
+-left-<i⁻ (suc x) lt = +-left-<i⁻ x (pred-≤i lt)

+-left-<i⁺ : {m n : Nat} -> (x : Nat) -> m <i n -> (x +' m) <i (x +' n)
+-left-<i⁺ zero    lt = lt
+-left-<i⁺ (suc x) lt = suc-≤i (+-left-<i⁺ x lt)

+-right-≤i⁺ : {m n : Nat} -> (x : Nat) -> m ≤i n -> (m +' x) ≤i (n +' x)
+-right-≤i⁺ {m} {n} x lt =
  transport (\k -> (+'-commute {x} {m} k) ≤i (+'-commute {x} {n} k)) (+-left-≤i⁺ x lt)

+-right-≤i⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) ≤i (n +' x) -> m ≤i n
+-right-≤i⁻ {m} {n} x lt =
  +-left-≤i⁻ x (transport (\k -> (+'-commute {m} {x} k) ≤i (+'-commute {n} {x} k)) lt)

+-right-<i⁺ : {m n : Nat} -> (x : Nat) -> m <i n -> (m +' x) <i (n +' x)
+-right-<i⁺ = +-right-≤i⁺

+-right-<i⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) <i (n +' x) -> m <i n
+-right-<i⁻ = +-right-≤i⁻

-- Transitive helpers
trans-≤i : {m n o : Nat} -> m ≤i n -> n ≤i o -> m ≤i o
trans-≤i zero-≤i      _           = zero-≤i
trans-≤i (suc-≤i lt1) (suc-≤i lt2) = suc-≤i (trans-≤i lt1 lt2)

trans-<i-≤i : {m n o : Nat} -> (m <i n) -> (n ≤i o) -> (m <i o)
trans-<i-≤i = trans-≤i

trans-≤i-<i : {m n o : Nat} -> m ≤i n -> n <i o -> m <i o
trans-≤i-<i zero-≤i      (suc-≤i _  ) = suc-≤i zero-≤i
trans-≤i-<i (suc-≤i lt1) (suc-≤i lt2) = suc-≤i (trans-≤i-<i lt1 lt2)

trans-<i : {m n o : Nat} -> (m <i n) -> (n <i o) -> (m <i o)
trans-<i lt1 lt2 = trans-≤i-<i (pred-≤i (right-suc-≤i lt1)) lt2

suc-monotonic-≤ : Monotonic _≤_ _≤_ suc
suc-monotonic-≤ a1 a2 a1≤a2 = suc-≤ a1≤a2
suc-monotonic-≥ : Monotonic _≥_ _≥_ suc
suc-monotonic-≥ a1 a2 a1≥a2 = suc-≤ a1≥a2
suc-monotonic-< : Monotonic _<_ _<_ suc
suc-monotonic-< a1 a2 a1<a2 = suc-≤ a1<a2
suc-monotonic-> : Monotonic _>_ _>_ suc
suc-monotonic-> a1 a2 a1>a2 = suc-≤ a1>a2


-- WellFounded
Acc-Nat< : (n : Nat) -> (x : Nat) -> (x < n) -> Acc _<_ x
Acc-Nat< zero x x<n = acc (\y y<x -> bot-elim (zero-≮ (trans-< y<x x<n)))
Acc-Nat< (suc n) x sx≤sn = acc (\y y<x -> Acc-Nat< n y (trans-<-≤ y<x (pred-≤ sx≤sn)))

WellFounded-Nat< : WellFounded _<_
WellFounded-Nat< n = Acc-Nat< (suc n) n refl-≤
