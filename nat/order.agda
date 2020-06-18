{-# OPTIONS --cubical --safe --exact-split #-}

module nat.order where

open import base
open import equality
open import nat.arithmetic
open import relation

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

data _≤_ : Nat -> Nat -> Set where
 zero-≤ : {n : Nat} -> zero ≤ n
 inc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = (suc m) ≤ n

_>_ : Nat -> Nat -> Set
m > n = n < m


zero-< : {n : Nat} -> zero < (suc n)
zero-< {n} = inc-≤ (zero-≤ {n})

inc-< : {m n : Nat} -> m < n -> suc m < suc n
inc-< = inc-≤


same-≤ : (n : Nat) -> n ≤ n
same-≤ zero = zero-≤
same-≤ (suc n) = inc-≤ (same-≤ n)

add1-< : (n : Nat) -> n < (suc n)
add1-< zero = zero-<
add1-< (suc n) = inc-< (add1-< n)

suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ (suc n)
suc-≤ zero-≤ = zero-≤
suc-≤ (inc-≤ p) = inc-≤ (suc-≤ p)

suc-< : {m n : Nat} -> m < n -> m < (suc n)
suc-< = suc-≤


trans-≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-≤ zero-≤ p = zero-≤
trans-≤ (inc-≤ l) (inc-≤ r) = inc-≤ (trans-≤ l r)

trans-< : {m n o : Nat} -> (m < n) -> (n < o) -> (m < o)
trans-< (inc-≤ zero-≤) (inc-≤ r) = zero-<
trans-< (inc-≤ l@(inc-≤ _)) (inc-≤ r) = inc-< (trans-< l r)

trans-<-≤ : {m n o : Nat} -> (m < n) -> (n ≤ o) -> (m < o)
trans-<-≤ (inc-≤ zero-≤) (inc-≤ r) = zero-<
trans-<-≤ (inc-≤ l@(inc-≤ _)) (inc-≤ r) = inc-< (trans-<-≤ l r)

trans-≤-< : {m n o : Nat} -> m ≤ n -> n < o -> m < o
trans-≤-< zero-≤ (inc-≤ _) = zero-<
trans-≤-< (inc-≤ l) (inc-≤ r) = inc-< (trans-≤-< l r)


absurd-same-< : {n : Nat} -> ¬ (n < n)
absurd-same-< (inc-≤ pr) = absurd-same-< pr


pred-≤ : {m n : Nat} -> m ≤ n -> pred m ≤ pred n
pred-≤ zero-≤ = zero-≤
pred-≤ (inc-≤ ≤) = ≤

dec-< : {m n : Nat} -> suc m < suc n -> m < n
dec-< (inc-≤ <) = <

≤->< : {m n : Nat} -> m ≤ n -> m < suc n
≤->< p = inc-≤ p


≤-a+'b==c'-Add : {a b c : Nat} -> Add c a b -> b ≤ c
≤-a+'b==c'-Add (add-zero b) = (same-≤ b)
≤-a+'b==c'-Add (add-suc p) = suc-≤ (≤-a+'b==c'-Add p)

≤-a+'b==c-Add : {a b c : Nat} -> Add c a b -> a ≤ c
≤-a+'b==c-Add pr = ≤-a+'b==c'-Add (add-commute pr)


≤-a+'b==c' : {a b c : Nat} -> a +' b == c -> b ≤ c
≤-a+'b==c' {a} {b} p = transport (\i -> b ≤ p i) (≤-a+'b==c'-Add (add a b))

≤-a+'b==c : {a b c : Nat} -> a +' b == c -> a ≤ c
≤-a+'b==c {a} {b} p = transport (\i -> a ≤ p i) (≤-a+'b==c-Add (add a b))

<-a+'b<c' : {a b c : Nat} -> (a +' b) < c -> b < c
<-a+'b<c' {zero} {b} {c} pr = pr
<-a+'b<c' {suc a} {b} {suc c} (inc-≤ pr) = suc-< (<-a+'b<c' pr)

<->!= : {m n : Nat} -> m < n -> m != n
<->!= (inc-≤ zero-≤) pr = zero-suc-absurd pr
<->!= (inc-≤ rec@(inc-≤ _)) p = (<->!= rec) (suc-injective p)

≤-antisym : {m n : Nat} -> m ≤ n -> n ≤ m -> m == n
≤-antisym zero-≤ zero-≤ = refl
≤-antisym (inc-≤ l) (inc-≤ r) = cong suc (≤-antisym l r)


≤->Σ' : {m n : Nat} -> m ≤ n -> Σ[ x ∈ Nat ] m +' x == n
≤->Σ' {m} {n} zero-≤ = (n , refl)
≤->Σ' (inc-≤ ≤) with (≤->Σ' ≤)
...                | (x , p) = (x , cong suc p)

≤->Σ : {m n : Nat} -> m ≤ n -> Σ[ x ∈ Nat ] x +' m == n
≤->Σ ≤ with (≤->Σ' ≤)
...       | (x , p) = (x , (+'-commute {x}) >=> p)

data _≤s_ : Nat -> Nat -> Set where
 refl-≤s : {m : Nat} -> m ≤s m
 step-≤s : {m n : Nat} -> m ≤s n -> m ≤s suc n

_<s_ : Nat -> Nat -> Set
m <s n = (suc m) ≤s n

inc-≤s : {m n : Nat} -> m ≤s n -> (suc m) ≤s (suc n)
inc-≤s refl-≤s = refl-≤s
inc-≤s (step-≤s rec) = step-≤s (inc-≤s rec)

zero-≤s : (m : Nat) -> 0 ≤s m
zero-≤s zero = refl-≤s
zero-≤s (suc n) = step-≤s (zero-≤s n)

≤s->≤ : {m n : Nat} -> m ≤s n -> m ≤ n
≤s->≤ {m} refl-≤s = same-≤ m
≤s->≤ (step-≤s rec) = suc-≤ (≤s->≤ rec)

≤->≤s : {m n : Nat} -> m ≤ n -> m ≤s n
≤->≤s (zero-≤ {n}) = zero-≤s n
≤->≤s (inc-≤ rec) = inc-≤s (≤->≤s rec)


-- strong-induction' :
--   {P : Nat -> Set} ->
--   P zero ->
--   ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
--   (m : Nat) -> {n : Nat} -> (n ≤ m) -> P n
-- strong-induction' z f zero id-≤ = z
-- strong-induction' z f (suc m) (inc-≤ rec-≤) = strong-induction' z f m rec-≤
-- strong-induction' z f (suc m) id-≤ = f {m} (strong-induction' z f m)
--
-- strong-induction :
--   {P : Nat -> Set} ->
--   P zero ->
--   ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
--   (m : Nat) -> P m
-- strong-induction z f m = strong-induction' z f m id-≤


decide-nat< : (x : Nat) -> (y : Nat) -> Dec (x < y)
decide-nat< _ zero = no \()
decide-nat< zero (suc n) = yes zero-<
decide-nat< (suc m) (suc n) with (decide-nat< m n)
... | yes pr = yes (inc-≤ pr)
... | no f = no (\ pr -> (f (pred-≤ pr)))
