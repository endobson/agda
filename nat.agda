{-# OPTIONS --cubical --safe --exact-split #-}

module nat where

open import base
open import equality
open import monoid
open import hlevel
open import relation
open import commutative-monoid

open import base using (Nat; zero; suc) public

Pos' : (n : Nat) -> Set
Pos' zero = Bot
Pos' (suc x) = Top

dec : (n : Nat) -> {Pos' n} -> Nat
dec (suc n) = n

dec0 : (n : Nat) -> Nat
dec0 zero = zero
dec0 (suc n) = n

suc-injective : {m n : Nat} -> suc m == suc n -> m == n
suc-injective p i = dec0 (p i)

infixl 6 _+'_
_+'_ : Nat -> Nat -> Nat
zero +' n = n
suc m +' n = suc (m +' n)

+'-right : {m n p : Nat} -> (n == p) -> m +' n == m +' p
+'-right {m} id = cong (\x -> m +' x) id

+'-left : {m n p : Nat} -> (n == p) -> n +' m == p +' m
+'-left {m} id = cong (\x -> x +' m) id

+'-cong : {m n p o : Nat} -> m == p -> n == o -> m +' n == p +' o
+'-cong = cong2 _+'_

+'-right-zero : {m : Nat} -> (m +' zero) == m
+'-right-zero {zero} = refl
+'-right-zero {suc m} = cong suc (+'-right-zero {m})

+'-left-zero : {m : Nat} -> (zero +' m) == m
+'-left-zero {m} = refl

+'-right-suc : {m n : Nat} -> (m +' (suc n)) == suc (m +' n)
+'-right-suc {zero} {n} = refl
+'-right-suc {suc m} {n} = cong suc (+'-right-suc {m} {n})

+'-commute : {m n : Nat} -> (m +' n) == (n +' m)
+'-commute {_} {zero} = +'-right-zero
+'-commute {m} {suc n} =
  begin
    m +' (suc n)
  ==< +'-right-suc >
    suc (m +' n)
  ==< cong suc (+'-commute {m}) >
    suc (n +' m)
  ==<>
    suc n +' m
  end

+'-assoc : {m n o : Nat} -> (m +' n) +' o == m +' (n +' o)
+'-assoc {zero} {_} {_} = refl
+'-assoc {suc m} {_} {_} = cong suc (+'-assoc {m})

iter : {A : Set} (n : Nat) (f : A -> A) -> A -> A
iter zero _ a = a
iter (suc n) f a = f (iter n f a)

infixl 7 _*'_
_*'_ : Nat -> Nat -> Nat
zero *' n = zero
suc m *' n = n +' (m *' n)

*'-distrib-+' : {m n p : Nat} -> (m +' n) *' p == (m *' p) +' (n *' p)
*'-distrib-+' {zero} = refl
*'-distrib-+' {suc m} {n} {p} =
  begin
    (suc m +' n) *' p
  ==<>
    p +' ((m +' n) *' p)
  ==< +'-right (*'-distrib-+' {m}) >
    p +' ((m *' p) +' (n *' p))
  ==< sym (+'-assoc {p}) >
    (suc m *' p) +' (n *' p)
  end

*'-right : {m n p : Nat} -> (n == p) -> m *' n == m *' p
*'-right {m} id = cong (\x -> m *' x) id

*'-left : {m n p : Nat} -> (n == p) -> n *' m == p *' m
*'-left {m} id = cong (\x -> x *' m) id

*'-cong : {m n p o : Nat} -> m == p -> n == o -> m *' n == p *' o
*'-cong = cong2 _*'_

*'-assoc : {m n p : Nat} -> (m *' n) *' p == m *' (n *' p)
*'-assoc {zero} {_} {_} = refl
*'-assoc {suc m} {n} {p} =
  begin
    (suc m *' n) *' p
  ==< (*'-distrib-+' {n} {m *' n} {p}) >
    (n *' p) +' (m *' n) *' p
  ==< +'-right (*'-assoc {m} {n} {p}) >
    (n *' p) +' m *' (n *' p)
  ==<>
    suc m *' (n *' p)
  end


*'-right-zero : {m : Nat} -> (m *' zero) == zero
*'-right-zero {zero} = refl
*'-right-zero {suc m} = *'-right-zero {m}

*'-right-suc : {m n : Nat} -> (m *' (suc n)) == m +' (m *' n)
*'-right-suc {zero} {n} = refl
*'-right-suc {suc m} {n} =
  begin
    (suc m *' suc n)
  ==<>
    suc n +' (m *' suc n)
  ==< +'-right (*'-right-suc {m} {n}) >
    suc n +' (m +' (m *' n))
  ==< sym (+'-assoc {suc n})>
    (suc n +' m) +' (m *' n)
  ==<>
    (suc (n +' m)) +' (m *' n)
  ==< +'-left (cong suc (+'-commute {n})) >
    (suc (m +' n)) +' (m *' n)
  ==<>
    (suc m +' n) +' (m *' n)
  ==< +'-assoc {suc m} >
    suc m +' (n  +' (m *' n))
  ==<>
    suc m +' (suc m *' n)
  end


*'-commute : {m n : Nat} -> (m *' n) == (n *' m)
*'-commute {zero} {n} = sym (*'-right-zero {n})
*'-commute {suc m} {n} =
  begin
    suc m *' n
  ==<>
    n +' m *' n
  ==< +'-right (*'-commute {m} {n}) >
    n +' n *' m
  ==< sym (*'-right-suc {n} {m}) >
    n *' suc m
  end


*'-left-one : {m : Nat} -> 1 *' m == m
*'-left-one {m} = refl >=> (+'-commute {m})

*'-right-one : {m : Nat} -> m *' 1 == m
*'-right-one {m} = *'-commute {m} >=> *'-left-one



zero-suc-absurd : {A : Set} {x : Nat} -> 0 == (suc x) -> A
zero-suc-absurd path = bot-elim (subst Pos' (sym path) tt)

*'-only-one-left : {m n : Nat} -> m *' n == 1 -> m == 1
*'-only-one-left {m} {zero} p = zero-suc-absurd (sym (*'-right-zero {m}) >=> p)
*'-only-one-left {zero} {(suc _)} p = zero-suc-absurd p
*'-only-one-left {suc zero} {suc zero} _ = refl
*'-only-one-left {suc zero} {suc (suc n)} p = zero-suc-absurd (sym (suc-injective p))
*'-only-one-left {suc (suc m)} {suc n} p =
  zero-suc-absurd ((sym (suc-injective p)) >=> (+'-commute {n}))

*'-only-one-right : {m n : Nat} -> m *' n == 1 -> n == 1
*'-only-one-right {m} {n} p = *'-only-one-left {n} {m} (*'-commute {n} {m} >=> p)


*'-distrib-+'-left : {m n p : Nat} -> m *' (n +' p) == (m *' n) +' (m *' p)
*'-distrib-+'-left {m} {n} {p} =
  begin
    m *' (n +' p)
  ==< (*'-commute {m} {n +' p}) >
    (n +' p) *' m
  ==< (*'-distrib-+' {n} {p} {m}) >
    n *' m +' p *' m
  ==< (+'-cong (*'-commute {n} {m}) (*'-commute {p} {m})) >
    (m *' n) +' (m *' p)
  end


data Fin : Nat -> Set where
 zero-fin : {n : Nat} -> Fin (suc n)
 suc-fin : {n : Nat} -> Fin n -> Fin (suc n)

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat zero-fin = zero
fin->nat (suc-fin f) = suc (fin->nat f)

fin->nat-injective : {n : Nat} {x y : Fin n} -> (fin->nat x) == (fin->nat y) -> x == y
fin->nat-injective {_} {zero-fin} {zero-fin} _ = refl
fin->nat-injective {_} {suc-fin x} {suc-fin y} pr =
  (cong suc-fin (fin->nat-injective (suc-injective pr)))
fin->nat-injective {_} {zero-fin} {suc-fin _} pr = bot-elim (zero-suc-absurd pr)
fin->nat-injective {_} {suc-fin _} {zero-fin} pr = bot-elim (zero-suc-absurd (sym pr))

nat->fin : (n : Nat) -> Fin (suc n)
nat->fin zero = zero-fin
nat->fin (suc n) = suc-fin (nat->fin n)


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


dec-≤ : {m n : Nat} -> suc m ≤ suc n -> m ≤ n
dec-≤ (inc-≤ ≤) = ≤

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


induction :
  {P : Nat -> Set} ->
  P zero ->
  ({m : Nat} -> P m -> P (suc m)) ->
  (m : Nat) -> P m
induction {P} z f zero = z
induction {P} z f (suc m) = f (induction {P} z f m)

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

decide-nat : (x : Nat) -> (y : Nat) -> Dec (x == y)
decide-nat zero zero = yes refl
decide-nat zero (suc n) = no (\ p -> zero-suc-absurd p)
decide-nat (suc m) zero = no (\ p -> zero-suc-absurd (sym p))
decide-nat (suc m) (suc n) with (decide-nat m n)
...  | (yes refl) = yes (cong suc refl)
...  | (no f) = no (\ pr -> f (suc-injective pr) )



decide-nat< : (x : Nat) -> (y : Nat) -> Dec (x < y)
decide-nat< _ zero = no \()
decide-nat< zero (suc n) = yes zero-<
decide-nat< (suc m) (suc n) with (decide-nat< m n)
... | yes pr = yes (inc-≤ pr)
... | no f = no (\ pr -> (f (dec-≤ pr)))


discreteNat : Discrete Nat
discreteNat = decide-nat

isSetNat : isSet Nat
isSetNat = Discrete->isSet discreteNat


instance
  NatMonoid+ : Monoid Nat
  NatMonoid+ = record {
    ε = 0;
    _∙_ = _+'_;
    ∙-assoc = \ {m} {n} {o} -> +'-assoc {m} {n} {o};
    ∙-left-ε = +'-left-zero;
    ∙-right-ε = +'-right-zero }

  NatCommMonoid+ : CommMonoid Nat
  NatCommMonoid+ = record
    { ∙-commute = (\ {m} {n} -> +'-commute {m} {n})
    }

  NatMonoid* : Monoid Nat
  NatMonoid* = record {
    ε = 1;
    _∙_ = _*'_;
    ∙-assoc = \ {m} {n} {o} -> *'-assoc {m} {n} {o};
    ∙-left-ε = *'-left-one;
    ∙-right-ε = *'-right-one }

  NatCommMonoid* : CommMonoid Nat
  NatCommMonoid* = record
    { ∙-commute = (\ {m} {n} -> *'-commute {m} {n})
    }
