{-# OPTIONS --cubical --safe --exact-split #-}

module nat.order where

open import base
open import equality
open import equivalence
open import isomorphism
open import nat.arithmetic
open import nat.properties
open import relation

data _≤_ : Nat -> Nat -> Set where
 zero-≤ : {n : Nat} -> zero ≤ n
 suc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_≥_ : Nat -> Nat -> Set
m ≥ n = m ≤ n

_<_ : Nat -> Nat -> Set
m < n = (suc m) ≤ n

_>_ : Nat -> Nat -> Set
m > n = n < m

zero-< : {n : Nat} -> zero < (suc n)
zero-< {n} = suc-≤ (zero-≤ {n})

suc-< : {m n : Nat} -> m < n -> suc m < suc n
suc-< = suc-≤


same-≤ : (n : Nat) -> n ≤ n
same-≤ zero = zero-≤
same-≤ (suc n) = suc-≤ (same-≤ n)

add1-< : (n : Nat) -> n < (suc n)
add1-< zero = zero-<
add1-< (suc n) = suc-< (add1-< n)

right-suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ (suc n)
right-suc-≤ zero-≤ = zero-≤
right-suc-≤ (suc-≤ p) = suc-≤ (right-suc-≤ p)

right-suc-< : {m n : Nat} -> m < n -> m < (suc n)
right-suc-< = right-suc-≤


trans-≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-≤ zero-≤ p = zero-≤
trans-≤ (suc-≤ l) (suc-≤ r) = suc-≤ (trans-≤ l r)

trans-< : {m n o : Nat} -> (m < n) -> (n < o) -> (m < o)
trans-< (suc-≤ zero-≤) (suc-≤ r) = zero-<
trans-< (suc-≤ l@(suc-≤ _)) (suc-≤ r) = suc-< (trans-< l r)

trans-<-≤ : {m n o : Nat} -> (m < n) -> (n ≤ o) -> (m < o)
trans-<-≤ (suc-≤ zero-≤) (suc-≤ r) = zero-<
trans-<-≤ (suc-≤ l@(suc-≤ _)) (suc-≤ r) = suc-< (trans-<-≤ l r)

trans-≤-< : {m n o : Nat} -> m ≤ n -> n < o -> m < o
trans-≤-< zero-≤ (suc-≤ _) = zero-<
trans-≤-< (suc-≤ l) (suc-≤ r) = suc-< (trans-≤-< l r)

absurd-same-< : {n : Nat} -> ¬ (n < n)
absurd-same-< (suc-≤ pr) = absurd-same-< pr

pred-≤ : {m n : Nat} -> m ≤ n -> pred m ≤ pred n
pred-≤ zero-≤ = zero-≤
pred-≤ (suc-≤ ≤) = ≤

-- suc-≤ introduces a path

suc-≤-iso : {m n : Nat} -> Iso (m ≤ n) (suc m ≤ suc n)
Iso.fun suc-≤-iso = suc-≤
Iso.inv suc-≤-iso = pred-≤
Iso.rightInv suc-≤-iso (suc-≤ _) = refl
Iso.leftInv  suc-≤-iso _         = refl

suc-≤-== : {m n : Nat} -> (m ≤ n) == (suc m ≤ suc n)
suc-≤-== = ua (isoToEquiv suc-≤-iso)

+-left-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (x +' m) ≤ (x +' n)
+-left-≤ {m} {n} x =
  induction {P = (\x -> m ≤ n == (x +' m) ≤ (x +' n))}
            refl (_>=> suc-≤-==) x

+-right-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (m +' x) ≤ (n +' x)
+-right-≤ {m} {n} x =
  transport (\i -> m ≤ n == (+'-commute {x} {m} i) ≤ (+'-commute {x} {n} i)) (+-left-≤ x)

<->!= : {m n : Nat} -> m < n -> m != n
<->!= (suc-≤ zero-≤) pr = zero-suc-absurd pr
<->!= (suc-≤ rec@(suc-≤ _)) p = (<->!= rec) (suc-injective p)

≤-antisym : {m n : Nat} -> m ≤ n -> n ≤ m -> m == n
≤-antisym zero-≤ zero-≤ = refl
≤-antisym (suc-≤ l) (suc-≤ r) = cong suc (≤-antisym l r)

-- Existential ≤
private
  data Add : Nat -> Nat -> Nat -> Set where
    add-zero : ∀ n -> Add n zero n
    add-suc : ∀ {a b c} -> Add a b c -> Add (suc a) (suc b) c

  add : (m : Nat) -> (n : Nat) -> Add (m +' n) m n
  add zero n = add-zero n
  add (suc m) n = add-suc (add m n)

  add-path-in : ∀ {a b c} -> a +' b == c -> Add c a b
  add-path-in {a} {b} p = (subst (\ c -> (Add c a b)) p (add a b))

  add-path-out : ∀ {a b c} -> Add c a b -> a +' b == c
  add-path-out (add-zero b) = refl
  add-path-out (add-suc p) = (cong suc (add-path-out p))

  add-commute : ∀ {a b c} -> Add c a b -> Add c b a
  add-commute {a} {b} pr = (add-path-in ((+'-commute {b} {a}) >=> (add-path-out pr)))

  ≤-a+'b==c'-Add : {a b c : Nat} -> Add c a b -> b ≤ c
  ≤-a+'b==c'-Add (add-zero b) = (same-≤ b)
  ≤-a+'b==c'-Add (add-suc p) = right-suc-≤ (≤-a+'b==c'-Add p)

  ≤-a+'b==c-Add : {a b c : Nat} -> Add c a b -> a ≤ c
  ≤-a+'b==c-Add pr = ≤-a+'b==c'-Add (add-commute pr)


≤-a+'b==c' : {a b c : Nat} -> a +' b == c -> b ≤ c
≤-a+'b==c' {a} {b} p = transport (\i -> b ≤ p i) (≤-a+'b==c'-Add (add a b))

≤-a+'b==c : {a b c : Nat} -> a +' b == c -> a ≤ c
≤-a+'b==c {a} {b} p = transport (\i -> a ≤ p i) (≤-a+'b==c-Add (add a b))

<-a+'b<c' : {a b c : Nat} -> (a +' b) < c -> b < c
<-a+'b<c' {zero} {b} {c} pr = pr
<-a+'b<c' {suc a} {b} {suc c} (suc-≤ pr) = right-suc-< (<-a+'b<c' pr)


≤->Σ' : {m n : Nat} -> m ≤ n -> Σ[ x ∈ Nat ] m +' x == n
≤->Σ' {m} {n} zero-≤ = (n , refl)
≤->Σ' (suc-≤ ≤) with (≤->Σ' ≤)
...                | (x , p) = (x , cong suc p)

≤->Σ : {m n : Nat} -> m ≤ n -> Σ[ x ∈ Nat ] x +' m == n
≤->Σ ≤ with (≤->Σ' ≤)
...       | (x , p) = (x , (+'-commute {x}) >=> p)

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
≤->≤s (zero-≤ {n}) = zero-≤s n
≤->≤s (suc-≤ rec) = suc-≤s (≤->≤s rec)

-- Decidable <
decide-nat< : (x : Nat) -> (y : Nat) -> Dec (x < y)
decide-nat< _ zero = no \()
decide-nat< zero (suc n) = yes zero-<
decide-nat< (suc m) (suc n) with (decide-nat< m n)
... | yes pr = yes (suc-≤ pr)
... | no f = no (\ pr -> (f (pred-≤ pr)))


-- strong-induction' :
--   {P : Nat -> Set} ->
--   P zero ->
--   ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
--   (m : Nat) -> {n : Nat} -> (n ≤ m) -> P n
-- strong-induction' z f zero id-≤ = z
-- strong-induction' z f (suc m) (suc-≤ rec-≤) = strong-induction' z f m rec-≤
-- strong-induction' z f (suc m) id-≤ = f {m} (strong-induction' z f m)
--
-- strong-induction :
--   {P : Nat -> Set} ->
--   P zero ->
--   ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
--   (m : Nat) -> P m
-- strong-induction z f m = strong-induction' z f m id-≤
