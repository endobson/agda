module hello-world where

infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_  #-}

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y 
cong f refl = refl

sym : {A : Set} -> {x y : A} -> x == y -> y == x 
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

infix  1 begin_
infixr 2 _==<>_ _==<_>_
infix  3 _end

begin_ : {A : Set} -> {x y : A} -> x == y -> x == y
begin x==y  =  x==y
 
_==<>_ : {A : Set} -> (x : A) {y : A} -> x == y -> x == y
x ==<> x==y  =  x==y
 
_==<_>_ : {A : Set} (x : A) {y z : A} -> x == y -> y == z -> x == z
x ==< x==y > y==z  = trans x==y y==z

_end : {A : Set} (x : A) -> x == x
x end  =  refl



infixl 20 _>=>_
_>=>_ : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
refl >=> refl = refl

data Nat : Set where
 zero : Nat
 suc : Nat -> Nat

data Int : Set where
 nonneg-int : Nat -> Int
 -- neg-int n Corresponds to  -(n+1)
 neg-int : Nat -> Int



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


*'-left-one : {m : Nat} -> (suc zero) *' m == m
*'-left-one {m} = refl >=> (+'-commute {m})
  
data _div_ : Nat -> Nat -> Set where
 div-exist : (a : Nat) -> (b : Nat) -> {c : Nat} -> {c *' a == b} -> a div b

div-refl : {n : Nat} -> n div n
div-refl {n} = (div-exist n n {suc zero} {*'-left-one})

div-trans : {d m n : Nat} -> d div m -> m div n -> d div n
div-trans (div-exist d m {a} {refl}) (div-exist m n {b} {refl}) = 
  div-exist d n {b *' a} {(*'-assoc {b})}

div-mult : {d n a : Nat} -> d div n -> (a *' d) div (a *' n)
div-mult {d} {n} {a} (div-exist d n {c} {refl}) =
  div-exist (a *' d) (a *' n) {c} 
  {begin
     c *' (a *' d)
   ==< sym (*'-assoc {c}) >
     (c *' a) *' d
   ==< *'-left (*'-commute {c} {a}) >
     (a *' c) *' d
   ==< *'-assoc {a}  >
     a *' (c *' d)
   ==<>
     a *' n
   end}


data PropEquiv : (A B : Set) -> Set where
 prop-equiv : {A B : Set} -> (A -> B) -> (B -> A) -> PropEquiv A B

data _≤'_ : Nat -> Nat -> Set where
 leq'-zero : {n : Nat} -> zero ≤' n
 leq'-suc : {m n : Nat} -> m ≤' n -> suc m ≤' suc n

data _≤_ : Nat -> Nat -> Set where
 leq-id : {n : Nat} -> n ≤ n
 leq-suc : {m n : Nat} -> m ≤ n -> m ≤ suc n

zero-≤ : (n : Nat) -> zero ≤ n
zero-≤ zero = leq-id
zero-≤ (suc n) = leq-suc (zero-≤ n)

inc-≤ : {m n : Nat} -> m ≤ n -> (suc m) ≤ (suc n)
inc-≤ leq-id = leq-id
inc-≤ (leq-suc p) = leq-suc (inc-≤ p)


same-≤' : (n : Nat) -> n ≤' n
same-≤' zero = leq'-zero
same-≤' (suc n) = leq'-suc (same-≤' n)

inc-≤' : {m n : Nat} -> m ≤' n -> m ≤' (suc n)
inc-≤' leq'-zero = leq'-zero
inc-≤' (leq'-suc p) = leq'-suc (inc-≤' p)


≤->≤' : {m n : Nat} -> m ≤ n -> m ≤' n
≤->≤' {m} leq-id = same-≤' m
≤->≤' (leq-suc p) = inc-≤' (≤->≤' p)


≤'->≤ : {m n : Nat} -> m ≤' n -> m ≤ n
≤'->≤ {_} {n} leq'-zero = zero-≤ n
≤'->≤ (leq'-suc p) = inc-≤ (≤'->≤ p)

≤'<->≤ : {m n : Nat} -> PropEquiv (m ≤' n) (m ≤ n)
≤'<->≤  = prop-equiv ≤'->≤ ≤->≤'
