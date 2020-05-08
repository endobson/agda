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
  
data Int : Set where
 zero-int : Int
 -- pos n Corresponds to (n+1)
 pos : Nat -> Int
 -- neg n Corresponds to -(n+1)
 neg : Nat -> Int

-_ : Int -> Int
- zero-int = zero-int
- (pos n) = neg n
- (neg n) = pos n

--double-inverse : {x : Nat} -> - - x == x
--double-inverse = refl

add1 : Int -> Int
add1 zero-int = pos zero
add1 (pos n) = (pos (suc n))
add1 (neg zero) = zero-int
add1 (neg (suc n)) = neg n

sub1 : Int -> Int
sub1 zero-int = neg zero
sub1 (neg n) = (neg (suc n))
sub1 (pos zero) = zero-int
sub1 (pos (suc n)) = pos n

_+_ : Int -> Int -> Int
zero-int + n = n
(pos (zero)) + n = add1 n
(pos (suc m')) + n = add1 ((pos m') + n)
(neg (zero)) + n = sub1 n
(neg (suc m')) + n = sub1 ((neg m') + n)

add1-sub1-id : {n : Int} -> add1 (sub1 n) == n
add1-sub1-id {zero-int} = refl
add1-sub1-id {pos zero} = refl
add1-sub1-id {pos (suc n')} = refl
add1-sub1-id {neg n'} = refl

sub1-add1-id : {n : Int} -> sub1 (add1 n) == n
sub1-add1-id {zero-int} = refl
sub1-add1-id {pos n'} = refl
sub1-add1-id {neg zero} = refl
sub1-add1-id {neg (suc n')} = refl

add1-extract-left : {m n : Int} -> add1 m + n == add1 (m + n)
sub1-extract-left : {m n : Int} -> sub1 m + n == sub1 (m + n)
add1-extract-left {zero-int} = refl
add1-extract-left {pos m'} = refl
add1-extract-left {neg zero} {n} rewrite add1-sub1-id {n} = refl
add1-extract-left {neg (suc m')} {n} = 
  begin
   add1 (neg (suc m')) + n
  ==<>
   neg m' + n
  ==< sym (add1-sub1-id {neg m' + n}) >
   add1 (sub1 (neg m' + n))
  ==< cong add1 (sym (sub1-extract-left {neg m'})) >
   add1 (sub1 (neg m') + n)
  ==<>
   add1 ((neg (suc m')) + n)
  end

sub1-extract-left {zero-int} = refl
sub1-extract-left {neg m'} = refl
sub1-extract-left {pos zero} {n} rewrite sub1-add1-id {n} = refl
sub1-extract-left {pos (suc m')} {n} =
  begin
   sub1 (pos (suc m')) + n
  ==<>
   pos m' + n
  ==< sym (sub1-add1-id {pos m' + n}) >
   sub1 (add1 (pos m' + n))
  ==< cong sub1 (sym (add1-extract-left {pos m'})) >
   sub1 (add1 (pos m') + n)
  ==<>
   sub1 ((pos (suc m')) + n)
  end

+-right : {m n p : Int} -> (n == p) -> m + n == m + p
+-right {m} id = cong (\x -> m + x) id

+-left : {m n p : Int} -> (n == p) -> n + m == p + m
+-left {m} id = cong (\x -> x + m) id

+-assoc : {m n o : Int} -> (m + n) + o == m + (n + o)
+-assoc {zero-int} = refl
+-assoc {pos zero} {n} {o} = add1-extract-left {n} {o}
+-assoc {neg zero} {n} {o} = sub1-extract-left {n} {o}
+-assoc {pos (suc m')} {n} {o} = 
  begin
    (pos (suc m') + n) + o
  ==<>
    (add1 (pos m') + n) + o
  ==< +-left (add1-extract-left {pos m'}) >
    (add1 (pos m' + n)) + o
  ==< add1-extract-left {pos m' + n} >
    add1 ((pos m' + n) + o)
  ==< cong add1 (+-assoc {pos m'}) >
    add1 (pos m' + (n + o))
  ==<>
    pos (suc m') + (n + o)
  end
+-assoc {neg (suc m')} {n} {o} = 
  begin
    (neg (suc m') + n) + o
  ==<>
    (sub1 (neg m') + n) + o
  ==< +-left (sub1-extract-left {neg m'}) >
    (sub1 (neg m' + n)) + o
  ==< sub1-extract-left {neg m' + n} >
    sub1 ((neg m' + n) + o)
  ==< cong sub1 (+-assoc {neg m'}) >
    sub1 (neg m' + (n + o))
  ==<>
    neg (suc m') + (n + o)
  end

+-right-zero : {m : Int} -> (m + zero-int) == m
+-right-zero {zero-int} = refl 
+-right-zero {pos zero} = refl
+-right-zero {neg zero} = refl
+-right-zero {pos (suc m)} = 
  begin
    (pos (suc m) + zero-int)
  ==<>
    add1 (pos m + zero-int)
  ==< cong add1 (+-right-zero {pos m}) >
    add1 (pos m)
  ==<>
    pos (suc m)
  end
+-right-zero {neg (suc m)} =
  begin
    (neg (suc m) + zero-int)
  ==<>
    sub1 (neg m + zero-int)
  ==< cong sub1 (+-right-zero {neg m}) >
    sub1 (neg m)
  ==<>
    neg (suc m)
  end

add1-extract-right : {m n : Int} -> m + add1 n == add1 (m + n)
add1-extract-right {zero-int} = refl
add1-extract-right {pos zero} {n} = refl
add1-extract-right {pos (suc m')} {n} = cong add1 (add1-extract-right {pos m'})
add1-extract-right {neg zero} {n}
  rewrite add1-sub1-id {n} | sub1-add1-id {n} =
  refl
add1-extract-right {neg (suc m')} {n} =
  begin
    neg (suc m') + add1 n
  ==<>
    sub1 (neg m') + add1 n
  ==< sub1-extract-left {neg m'}  >
    sub1 (neg m' + add1 n)
  ==< cong sub1 (add1-extract-right {neg m'}) >
    sub1 (add1 (neg m' + n))
  ==< sub1-add1-id >
    neg m' + n
  ==< sym add1-sub1-id >
    add1 (sub1 (neg m' + n))
  ==< cong add1 (sym (sub1-extract-left {neg m'})) >
    add1 (sub1 (neg m') + n)
  ==<>
    (add1 (neg (suc m') + n))
  end

sub1-extract-right : {m n : Int} -> m + sub1 n == sub1 (m + n)
sub1-extract-right {zero-int} = refl
sub1-extract-right {neg zero} {n} = refl
sub1-extract-right {neg (suc m')} {n} = cong sub1 (sub1-extract-right {neg m'})
sub1-extract-right {pos zero} {n}
  rewrite sub1-add1-id {n} | add1-sub1-id {n} =
  refl
sub1-extract-right {pos (suc m')} {n} =
  begin
    pos (suc m') + sub1 n
  ==<>
    add1 (pos m') + sub1 n
  ==< add1-extract-left {pos m'}  >
    add1 (pos m' + sub1 n)
  ==< cong add1 (sub1-extract-right {pos m'}) >
    add1 (sub1 (pos m' + n))
  ==< add1-sub1-id >
    pos m' + n
  ==< sym sub1-add1-id >
    sub1 (add1 (pos m' + n))
  ==< cong sub1 (sym (add1-extract-left {pos m'})) >
    sub1 (add1 (pos m') + n)
  ==<>
    (sub1 (pos (suc m') + n))
  end

+-commute : {m n : Int} -> (m + n) == (n + m)
+-commute {zero-int} = sym +-right-zero
+-commute {pos zero} {n} =
 begin
   pos zero + n
 ==<>
   add1 n
 ==< cong add1 (sym +-right-zero) >
   add1 (n + zero-int)
 ==< sym (add1-extract-right {n}) >
   n + add1 zero-int
 ==<>
   n + pos zero
 end 
+-commute {neg zero} {n} =
 begin
   neg zero + n
 ==<>
   sub1 n
 ==< cong sub1 (sym +-right-zero) >
   sub1 (n + zero-int)
 ==< sym (sub1-extract-right {n}) >
   n + sub1 zero-int
 ==<>
   n + neg zero
 end 
+-commute {pos (suc m')} {n} = 
  begin
    pos (suc m') + n
  ==<>
    add1 (pos m' + n)
  ==< cong add1 (+-commute {pos m'}) >
    add1 (n + pos m')
  ==< sym (add1-extract-right {n})>
    n + add1 (pos m')
  ==<>
    n + pos (suc m')
  end
+-commute {neg (suc m')} {n} = 
  begin
    neg (suc m') + n
  ==<>
    sub1 (neg m' + n)
  ==< cong sub1 (+-commute {neg m'}) >
    sub1 (n + neg m')
  ==< sym (sub1-extract-right {n})>
    n + sub1 (neg m')
  ==<>
    n + neg (suc m')
  end



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

div-one : {n : Nat} -> (1 div n)
div-one {n} = div-exist 1 n {n} {*'-right-one {n}}

div-only-one : {n : Nat} -> (n div 1) -> n == 1
div-only-one {n} (div-exist n 1 {c} {p}) = *'-only-one-right {c} {n} p


data GCD : Nat -> Nat -> Nat -> Set where
 gcd : (a : Nat) -> (b : Nat) -> (d : Nat) -> (d div a) -> (d div b)
       -> ((x : Nat) -> x div a -> x div b -> x div d) -> GCD a b d

data LinearCombination : Nat -> Nat -> Nat -> Set where
 gcd-sum : (a : Nat) -> (b : Nat) -> {d : Nat} -> {x : Nat} -> {y : Nat} 
   -> {a *' x +' d == b *' y}
   -> LinearCombination a b d

ex1-1 : {a b c d : Nat} -> GCD a b 1 -> c div a -> d div b -> GCD c d 1 
ex1-1 {a} {b} {c} {d} (gcd a b 1 _ _ gcd-f) c-div-a d-div-b = 
  gcd c d 1 div-one div-one 
  (\x x-div-c x-div-d -> 
    (gcd-f x (div-trans x-div-c c-div-a) (div-trans x-div-d d-div-b)))

-- ex1-2 : {a b c : Nat} -> GCD a b 1 -> GCD a c 1 -> GCD a (b *' c) 1
-- ex1-2 {a} {b} {c} (gcd a b 1 _ _ _) (gcd a c 1 _ _ _)  =
--   gcd a (b *' c) 1 div-one div-one
--   (\x x-div-a x-div-bc -> 
--     ?)



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
