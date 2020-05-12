module nat where

open import equality

data Nat : Set where
 zero : Nat
 suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infixl 6 _+'_
_+'_ : Nat -> Nat -> Nat
zero +' n = n
suc m +' n = suc (m +' n)

+'-right : {m n p : Nat} -> (n == p) -> m +' n == m +' p
+'-right {m} id = cong (\x -> m +' x) id

+'-left : {m n p : Nat} -> (n == p) -> n +' m == p +' m
+'-left {m} id = cong (\x -> x +' m) id

+'-right-zero : {m : Nat} -> (m +' zero) == m
+'-right-zero {zero} = refl 
+'-right-zero {suc m} = cong suc (+'-right-zero {m})

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


zero-one-absurd : {A : Set} -> 0 == 1 -> A
zero-one-absurd ()

*'-only-one-left : {m n : Nat} -> m *' n == 1 -> m == 1
*'-only-one-left {zero} {_} ()
*'-only-one-left {m} {zero} p = zero-one-absurd (sym (*'-right-zero {m}) >=> p)
*'-only-one-left {suc zero} {suc zero} _ = refl

*'-only-one-right : {m n : Nat} -> m *' n == 1 -> n == 1
*'-only-one-right {zero} {_} ()
*'-only-one-right {m} {zero} p = zero-one-absurd (sym (*'-right-zero {m}) >=> p)
*'-only-one-right {suc zero} {suc zero} _ = refl

data Fin : Nat -> Set where
 zero-fin : {n : Nat} -> Fin (suc n)
 suc-fin : {n : Nat} -> Fin n -> Fin (suc n)

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat zero-fin = zero
fin->nat (suc-fin f) = suc (fin->nat f)

nat->fin : (n : Nat) -> Fin (suc n)
nat->fin zero = zero-fin
nat->fin (suc n) = suc-fin (nat->fin n)


data _≤'_ : Nat -> Nat -> Set where
 zero-≤' : {n : Nat} -> zero ≤' n
 inc-≤' : {m n : Nat} -> m ≤' n -> suc m ≤' suc n

data _<'_ : Nat -> Nat -> Set where
 zero-<' : {n : Nat} -> zero <' (suc n)
 inc-<' : {m n : Nat} -> m <' n -> suc m <' suc n

data _≤_ : Nat -> Nat -> Set where
 id-≤ : {n : Nat} -> n ≤ n
 suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ suc n

private
  data _<_ : Nat -> Nat -> Set where
    add1-< : {n : Nat} -> n < (suc n)
    suc-< : {m n : Nat} -> m < n -> m < suc n

inc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n
inc-≤ id-≤ = id-≤
inc-≤ (suc-≤ ≤) = suc-≤ (inc-≤ ≤)

inc-< : {m n : Nat} -> m < n -> suc m < suc n
inc-< add1-< = add1-< 
inc-< (suc-< <) = suc-< (inc-< <)

zero-≤ : (n : Nat) -> zero ≤ n
zero-≤ zero = id-≤
zero-≤ (suc n) = suc-≤ (zero-≤ n)

zero-< : (n : Nat) -> zero < (suc n)
zero-< zero = add1-<
zero-< (suc n) = suc-< (zero-< n)

same-≤' : (n : Nat) -> n ≤' n
same-≤' zero = zero-≤'
same-≤' (suc n) = inc-≤' (same-≤' n)

add1-<' : (n : Nat) -> n <' (suc n)
add1-<' zero = zero-<'
add1-<' (suc n) = inc-<' (add1-<' n)

suc-≤' : {m n : Nat} -> m ≤' n -> m ≤' (suc n)
suc-≤' zero-≤' = zero-≤'
suc-≤' (inc-≤' p) = inc-≤' (suc-≤' p)

suc-<' : {m n : Nat} -> m <' n -> m <' (suc n)
suc-<' zero-<' = zero-<'
suc-<' (inc-<' p) = inc-<' (suc-<' p)


≤->≤' : {m n : Nat} -> m ≤ n -> m ≤' n
≤->≤' {m} id-≤ = same-≤' m
≤->≤' (suc-≤ p) = suc-≤' (≤->≤' p)
 
<-><' : {m n : Nat} -> m < n -> m <' n
<-><' {m} add1-< = add1-<' m
<-><' (suc-< p) = suc-<' (<-><' p)

≤'->≤ : {m n : Nat} -> m ≤' n -> m ≤ n
≤'->≤ {_} {n} zero-≤' = zero-≤ n
≤'->≤ (inc-≤' p) = inc-≤ (≤'->≤ p)

<'->< : {m n : Nat} -> m <' n -> m < n
<'->< {_} {suc n} zero-<' = zero-< n
<'->< (inc-<' p) = inc-< (<'->< p)

≤->< : {m n : Nat} -> m ≤ n -> m < suc n
≤->< {m} id-≤ = add1-< {m}
≤->< (suc-≤ p) = suc-< (≤->< p)

≤'-><' : {m n : Nat} -> m ≤' n -> m <' suc n
≤'-><' {m} {n} zero-≤' = zero-<' {n}
≤'-><' (inc-≤' p) = inc-<' (≤'-><' p)


trans-≤' : {m n o : Nat} -> m ≤' n -> n ≤' o -> m ≤' o
trans-≤' zero-≤' p = zero-≤'
trans-≤' (inc-≤' l) (inc-≤' r) = inc-≤' (trans-≤' l r)

trans-≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-≤ a b = ≤'->≤ (trans-≤' (≤->≤' a) (≤->≤' b))

trans-<'-≤' : {m n o : Nat} -> m <' n -> n ≤' o -> m <' o
trans-<'-≤' {zero} zero-<' (inc-≤' _) = zero-<'
trans-<'-≤' (inc-<' l) (inc-≤' r) = inc-<' (trans-<'-≤' l r)

trans-<-≤ : {m n o : Nat} -> m < n -> n ≤ o -> m < o
trans-<-≤ a b = <'->< (trans-<'-≤' (<-><' a) (≤->≤' b))


absurd-same-<' : {n : Nat} -> ¬ (n <' n)
absurd-same-<' (inc-<' pr) = absurd-same-<' pr

absurd-same-< : {n : Nat} -> ¬ (n < n)
absurd-same-< pr = absurd-same-<' (<-><' pr)


dec-≤' : {m n : Nat} -> suc m ≤' suc n -> m ≤' n
dec-≤' (inc-≤' ≤) = ≤

dec-<' : {m n : Nat} -> suc m <' suc n -> m <' n
dec-<' (inc-<' <) = <

dec-≤ : {m n : Nat} -> suc m ≤ suc n -> m ≤ n
dec-≤ p = ≤'->≤ (dec-≤' (≤->≤' p))

dec-< : {m n : Nat} -> suc m < suc n -> m < n
dec-< p = <'->< (dec-<' (<-><' p))


≤-a+'b==c : {a b c : Nat} -> a +' b == c -> b ≤ c
≤-a+'b==c {zero} {b} {c} refl = id-≤
≤-a+'b==c {suc a} {b} {suc c} refl = suc-≤ (≤-a+'b==c {a} {b} {c} refl)

≤'-a+'b==c : {a b c : Nat} -> a +' b == c -> b ≤' c
≤'-a+'b==c pr = ≤->≤' (≤-a+'b==c pr)


<'-a+'b<c : {a b c : Nat} -> (a +' b) <' c -> b <' c
<'-a+'b<c {zero} {b} {c} pr = pr
<'-a+'b<c {suc a} {b} {suc c} (inc-<' pr) = suc-<' (<'-a+'b<c pr)


<-a+'b<c : {a b c : Nat} -> (a +' b) < c -> b < c
<-a+'b<c p = <'->< (<'-a+'b<c (<-><' p))

induction : 
  {P : Nat -> Set} ->
  P zero ->
  ({m : Nat} -> P m -> P (suc m)) ->
  (m : Nat) -> P m
induction {P} z f zero = z
induction {P} z f (suc m) = f (induction {P} z f m)

strong-induction' : 
  {P : Nat -> Set} ->
  P zero ->
  ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
  (m : Nat) -> {n : Nat} -> (n ≤ m) -> P n
strong-induction' z f zero id-≤ = z
strong-induction' z f (suc m) (suc-≤ rec-≤) = strong-induction' z f m rec-≤
strong-induction' z f (suc m) id-≤ = f {m} (strong-induction' z f m)

strong-induction : 
  {P : Nat -> Set} ->
  P zero ->
  ({m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m)) ->
  (m : Nat) -> P m
strong-induction z f m = strong-induction' z f m id-≤

suc-injective :  {m n : Nat} -> suc m == suc n -> m == n
suc-injective refl = refl

decide-nat : (x : Nat) -> (y : Nat) -> Dec (x == y)
decide-nat zero zero = yes refl
decide-nat zero (suc n) = no (\ () )
decide-nat (suc m) zero = no (\ () )
decide-nat (suc m) (suc n) with (decide-nat m n) 
...  | (yes refl) = yes refl
...  | (no f) = no (\ pr -> f (suc-injective pr) )
