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
 suc-≤' : {m n : Nat} -> m ≤' n -> suc m ≤' suc n

data _≤_ : Nat -> Nat -> Set where
 id-≤ : {n : Nat} -> n ≤ n
 suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ suc n

inc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n
inc-≤ id-≤ = id-≤
inc-≤ (suc-≤ ≤) = suc-≤ (inc-≤ ≤)

zero-≤ : (n : Nat) -> zero ≤ n
zero-≤ zero = id-≤
zero-≤ (suc n) = suc-≤ (zero-≤ n)

same-≤' : (n : Nat) -> n ≤' n
same-≤' zero = zero-≤'
same-≤' (suc n) = suc-≤' (same-≤' n)

inc-≤' : {m n : Nat} -> m ≤' n -> m ≤' (suc n)
inc-≤' zero-≤' = zero-≤'
inc-≤' (suc-≤' p) = suc-≤' (inc-≤' p)

≤->≤' : {m n : Nat} -> m ≤ n -> m ≤' n
≤->≤' {m} id-≤ = same-≤' m
≤->≤' (suc-≤ p) = inc-≤' (≤->≤' p)
 
 
≤'->≤ : {m n : Nat} -> m ≤' n -> m ≤ n
≤'->≤ {_} {n} zero-≤' = zero-≤ n
≤'->≤ (suc-≤' p) = inc-≤ (≤'->≤ p)


trans-≤' : {m n o : Nat} -> m ≤' n -> n ≤' o -> m ≤' o
trans-≤' zero-≤' p = zero-≤'
trans-≤' (suc-≤' l) (suc-≤' r) = suc-≤' (trans-≤' l r)

trans-≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-≤ a b = ≤'->≤ (trans-≤' (≤->≤' a) (≤->≤' b))

dec-≤' : {m n : Nat} -> suc m ≤' suc n -> m ≤' n
dec-≤' (suc-≤' ≤) = ≤

dec-≤ : {m n : Nat} -> suc m ≤ suc n -> m ≤ n
dec-≤ p = ≤'->≤ (dec-≤' (≤->≤' p))

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

  
data Int : Set where
 zero-int : Int
 -- pos n Corresponds to (n+1)
 pos : Nat -> Int
 -- neg n Corresponds to -(n+1)
 neg : Nat -> Int

int : Nat -> Int
int zero = zero-int
int (suc n) = pos n

infix 9 -_
-_ : Int -> Int
- zero-int = zero-int
- (pos n) = neg n
- (neg n) = pos n

minus : Int -> Int
minus n = - n

minus-double-inverse : {x : Int} -> - - x == x
minus-double-inverse {zero-int} = refl
minus-double-inverse {pos x'} = refl
minus-double-inverse {neg x'} = refl

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

infixl 6 _+_
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

add1-minus->minus-sub1 : {n : Int} -> add1 (- n) == - (sub1 n)
add1-minus->minus-sub1 {zero-int} = refl
add1-minus->minus-sub1 {neg _} = refl
add1-minus->minus-sub1 {pos zero} = refl
add1-minus->minus-sub1 {pos (suc n')} = refl

sub1-minus->minus-add1 : {n : Int} -> sub1 (- n) == - (add1 n)
sub1-minus->minus-add1 {zero-int} = refl
sub1-minus->minus-add1 {pos _} = refl
sub1-minus->minus-add1 {neg zero} = refl
sub1-minus->minus-add1 {neg (suc n')} = refl


add-minus-zero : {n : Int} -> n + - n == zero-int
add-minus-zero {zero-int} = refl
add-minus-zero {pos zero} = refl
add-minus-zero {neg zero} = refl
add-minus-zero {pos (suc n')} = 
  begin
    pos (suc n') + - pos (suc n')
  ==<>
    add1 (pos n') + - add1 (pos n')
  ==< add1-extract-left {pos n'} >
    add1 ((pos n') + - add1 (pos n'))
  ==< sym (add1-extract-right {pos n'}) >
    (pos n') + add1 (- add1 (pos n'))
  ==< +-right {pos n'} (add1-minus->minus-sub1 {add1 (pos n')}) >
    (pos n') + - (sub1 (add1 (pos n')))
  ==< +-right {pos n'} (cong minus (sub1-add1-id)) >
    pos n' + - pos n'
  ==< add-minus-zero {pos n'}  >
    zero-int
  end
add-minus-zero {neg (suc n')} = 
  begin
    neg (suc n') + - neg (suc n')
  ==<>
    sub1 (neg n') + - sub1 (neg n')
  ==< sub1-extract-left {neg n'} >
    sub1 ((neg n') + - sub1 (neg n'))
  ==< sym (sub1-extract-right {neg n'}) >
    (neg n') + sub1 (- sub1 (neg n'))
  ==< +-right {neg n'} (sub1-minus->minus-add1 {sub1 (neg n')}) >
    (neg n') + - (add1 (sub1 (neg n')))
  ==< +-right {neg n'} (cong minus (add1-sub1-id)) >
    neg n' + - neg n'
  ==< add-minus-zero {neg n'}  >
    zero-int
  end

minus-distrib-+ : {m n : Int} -> - (m + n) == - m + - n
minus-distrib-+ {zero-int} = refl
minus-distrib-+ {pos zero} = sym sub1-minus->minus-add1
minus-distrib-+ {neg zero} = sym add1-minus->minus-sub1
minus-distrib-+ {pos (suc m')} {n} =
  begin
    - (pos (suc m') + n)
  ==<>
    - (add1 (pos m' + n))
  ==< sym sub1-minus->minus-add1 >
    sub1 (- (pos m' + n))
  ==< cong sub1 (minus-distrib-+ {pos m'}) >
    sub1 (- pos m' + - n)
  ==< sym (sub1-extract-left { - pos m'}) >
    sub1 (- (pos m')) + - n
  ==< +-left (sub1-minus->minus-add1 {pos m'}) >
    - (add1 (pos m')) + - n
  ==<>
    - (pos (suc m')) + - n
  end
minus-distrib-+ {neg (suc m')} {n} =
  begin
    - (neg (suc m') + n)
  ==<>
    - (sub1 (neg m' + n))
  ==< sym add1-minus->minus-sub1 >
    add1 (- (neg m' + n))
  ==< cong add1 (minus-distrib-+ {neg m'}) >
    add1 (- neg m' + - n)
  ==< sym (add1-extract-left { - neg m'}) >
    add1 (- (neg m')) + - n
  ==< +-left (add1-minus->minus-sub1 {neg m'}) >
    - (sub1 (neg m')) + - n
  ==<>
    - (neg (suc m')) + - n
  end


infixl 7 _*nz_
_*nz_ : Nat -> Int -> Int
zero *nz m = zero-int
suc n *nz m = m + n *nz m


infixl 7 _*_
_*_ : Int -> Int -> Int
zero-int * n = zero-int
pos m * n = suc m *nz n
neg m * n = -(suc m *nz n)

*-right : {m n p : Int} -> (n == p) -> m * n == m * p
*-right {m} id = cong (\x -> m * x) id

*-left : {m n p : Int} -> (n == p) -> n * m == p * m
*-left {m} id = cong (\x -> x * m) id

minus-extract-left : {m n : Int} -> - m * n == - (m * n)
minus-extract-left {zero-int} = refl
minus-extract-left {pos m'} = refl
minus-extract-left {neg m'} {n} = sym (minus-double-inverse {pos m' * n})

*-right-zero : {m : Int} -> m * zero-int == zero-int
*-right-zero {zero-int} = refl
*-right-zero {pos zero} = refl
*-right-zero {neg zero} = refl
*-right-zero {pos (suc m')} = *-right-zero {pos m'}
*-right-zero {neg (suc m')} = *-right-zero {neg m'}

*-right-one : {m : Int} -> m * (pos zero) == m
*-right-one {zero-int} = refl
*-right-one {pos zero} = refl
*-right-one {neg zero} = refl
*-right-one {pos (suc m')} = cong add1 (*-right-one {pos m'})
*-right-one {neg (suc m')} = cong minus (+-right {pos zero} (*-right-one {pos m'}))

*-right-negative-one : {m : Int} -> m * (neg zero) == - m
*-right-negative-one {zero-int} = refl
*-right-negative-one {pos zero} = refl
*-right-negative-one {neg zero} = refl
*-right-negative-one {pos (suc m')} = cong sub1 (*-right-negative-one {pos m'})
*-right-negative-one {neg (suc m')} = cong minus (+-right {neg zero} (*-right-negative-one {pos m'}))


add1-extract-* : {m n : Int} -> add1 m * n == n + m * n
add1-extract-* {zero-int} = refl
add1-extract-* {pos m'} = refl
add1-extract-* {neg zero} {n} =
  begin
    add1 (neg zero) * n
  ==<>
    zero-int
  ==< sym (add-minus-zero {n}) >
    n + - n 
  ==< (+-right {n} (cong minus (sym (+-right-zero {n})))) >
    n + - (n + zero-int)
  ==<>
    n + (neg zero) * n
  end
add1-extract-* {neg (suc m')} {n} =
  begin
    add1 (neg (suc m')) * n
  ==<>
    neg m' * n
  ==<>
    - (pos m' * n)
  ==<>
    (zero-int) + - ((pos m') * n)
  ==< +-left (sym (add-minus-zero {n})) >
    (n + - n) + - ((pos m') * n)
  ==< +-assoc {n} >
    n + (- n + - ((pos m') * n))
  ==< +-right {n} (sym (minus-distrib-+ {n})) >
    n + (- (n + (pos m') * n))
  ==<>
    n + (neg (suc m')) * n
  end

add1-extract-*-right : {m n : Int} -> m * add1 n == m + m * n
add1-extract-*-right {zero-int} = refl
add1-extract-*-right {neg zero} {n} =
  begin
    neg zero * add1 n 
  ==<>
    - (add1 n + zero-int)
  ==< cong minus (add1-extract-left {n}) >
    - add1 (n + zero-int)
  ==< sym sub1-minus->minus-add1 >
    sub1 (- (n + zero-int))
  ==<>
    neg zero + neg zero * n
  end
add1-extract-*-right {pos zero} {n} = (add1-extract-left {n})
add1-extract-*-right {neg (suc m')} {n} =
  begin
    neg (suc m') * add1 n 
  ==<>
    - (add1 n + pos m' * add1 n)
  ==< cong minus (+-right {add1 n} (add1-extract-*-right {pos m'} {n})) >
    - (add1 n + (pos m' + pos m' * n))
  ==< cong minus (sym (+-assoc {add1 n})) >
    - ((add1 n + pos m') + pos m' * n)
  ==< cong minus (+-left (add1-extract-left {n} {pos m'})) >
    - (add1 (n + pos m') + pos m' * n)
  ==< cong minus (+-left (cong add1 (+-commute {n}))) >
    - (add1 (pos m' + n) + pos m' * n)
  ==< cong minus (+-left (sym (add1-extract-left {pos m'}))) > 
    - ((add1 (pos m') + n) + pos m' * n)
  ==< cong minus (+-assoc {add1 (pos m')}) >
    - (add1 (pos m') + (n + pos m' * n))
  ==< minus-distrib-+ {add1 (pos m')} >
    - add1 (pos m') + - (n + pos m' * n)
  ==<>
    neg (suc m') + neg (suc m') * n
  end
add1-extract-*-right {pos (suc m')} {n} =
  begin
    pos (suc m') * add1 n 
  ==<>
    add1 n + pos m' * add1 n
  ==< +-right {add1 n} (add1-extract-*-right {pos m'} {n}) >
    add1 n + (pos m' + pos m' * n)
  ==< sym (+-assoc {add1 n}) >
    (add1 n + pos m') + pos m' * n
  ==< +-left (add1-extract-left {n}) >
    add1 (n + pos m') + pos m' * n
  ==< +-left (cong add1 (+-commute {n})) >
    add1 (pos m' + n) + pos m' * n
  ==< +-left (sym (add1-extract-left {pos m'} {n})) >
    (add1 (pos m') + n) + pos m' * n
  ==< +-assoc {add1 (pos m')} >
    pos (suc m') + pos (suc m') * n
  end


sub1-extract-* : {m n : Int} -> sub1 m * n == - n + m * n
sub1-extract-* {zero-int} {n} = 
  begin
    sub1 zero-int * n
  ==<>
    - (n + zero-int)
  ==< cong minus (+-right-zero) >
    - n
  ==< sym +-right-zero >
    - n + zero-int * n
  end
sub1-extract-* {pos zero} {n} =
  begin
    sub1 (pos zero) * n
  ==<>
    zero-int
  ==< sym (add-minus-zero {n}) >
    n + - n
  ==< +-commute {n} >
    - n + n
  ==< +-right { - n} (sym (+-right-zero {n})) >
    - n + (n + zero-int)
  ==<>
    - n + (pos zero) * n
  end
sub1-extract-* {pos (suc m')} {n} =
  begin
    sub1 (pos (suc m')) * n
  ==<>
    (pos m') * n
  ==< +-left (sym (add-minus-zero {n})) >
    (n + - n) + (pos m') * n
  ==< +-left (+-commute {n}) >
    (- n + n) + (pos m') * n
  ==< +-assoc { - n} >
    - n + (n + (pos m') * n)
  ==<>
    - n + (pos (suc m')) * n
  end
sub1-extract-* {neg m'} {n} =
  begin
    sub1 (neg m') * n
  ==<>
    - (add1 (pos m') * n)
  ==< cong minus (add1-extract-* {pos m'} {n}) >
    - (n + (pos m') * n)
  ==< minus-distrib-+ {n} >
    - n + (neg m') * n
  end


sub1-extract-*-right : {m n : Int} -> m * sub1 n == - m + m * n
sub1-extract-*-right {zero-int} = refl
sub1-extract-*-right {pos zero} {n} = 
  begin
    (pos zero) * (sub1 n)
  ==< +-right-zero {sub1 n} >
    (sub1 n)
  ==< cong sub1 (sym (+-right-zero)) >
    (sub1 (n + zero-int))
  ==<>
    - (pos zero) + (pos zero) * n
  end
sub1-extract-*-right {neg zero} {n} =
  begin
    (neg zero) * (sub1 n)
  ==< cong minus (+-right-zero {sub1 n}) >
    - (sub1 n)
  ==< sym (add1-minus->minus-sub1 {n}) >
    add1 (- n)
  ==< cong add1 (cong minus (sym (+-right-zero))) >
    add1 (- (n + zero-int))
  ==<>
    - (neg zero) + (neg zero) * n
  end
sub1-extract-*-right {pos (suc m')} {n} =
  begin
    (pos (suc m')) * (sub1 n)
  ==<>
    sub1 n + pos m' * sub1 n
  ==< +-right {sub1 n} (sub1-extract-*-right {pos m'} {n}) >
    sub1 n + (- pos m' + pos m' * n)
  ==< sym (+-assoc {sub1 n}) >
    (sub1 n + - pos m') + (pos m') * n
  ==< +-left (sub1-extract-left {n}) >
    sub1 (n + - pos m') + (pos m') * n
  ==< +-left (cong sub1 (+-commute {n})) >
    sub1 (- pos m' + n) + (pos m') * n
  ==< +-left (sym (sub1-extract-left { - pos m'})) >
    (sub1 (- pos m') + n) + (pos m') * n
  ==< +-assoc {sub1 (- pos m')} >
    sub1 (- pos m') + (n + (pos m') * n)
  ==<>
    - (pos (suc m')) + (pos (suc m')) * n
  end
sub1-extract-*-right {neg (suc m')} {n} =
  begin
    (neg (suc m')) * (sub1 n)
  ==<>
    - (sub1 n + pos m' * sub1 n)
  ==< minus-distrib-+ {sub1 n} >
    - sub1 n + neg m' * sub1 n
  ==< +-right { - sub1 n} (sub1-extract-*-right {neg m'} {n}) >
    - sub1 n + (- neg m' + neg m' * n)
  ==< sym (+-assoc { - sub1 n}) >
    (- sub1 n + - neg m') + neg m' * n
  ==< +-left (sym (minus-distrib-+ {sub1 n})) >
    - (sub1 n + neg m') + neg m' * n
  ==< +-left (cong minus (sub1-extract-left {n})) >
    - sub1 (n + neg m') + neg m' * n
  ==< +-left (cong minus (cong sub1 (+-commute {n}))) >
    - sub1 (neg m' + n) + neg m' * n
  ==< +-left (cong minus (sym (sub1-extract-left {neg m'}))) >
    - (sub1 (neg m') + n) + neg m' * n
  ==< +-left (minus-distrib-+ {sub1 (neg m')}) >
    (- sub1 (neg m') + - n) + neg m' * n
  ==< +-assoc { - sub1 (neg m')} >
    - sub1 (neg m') + (- n + neg m' * n)
  ==< +-right { - sub1 (neg m')} (sym (minus-distrib-+ {n})) >
    - (neg (suc m')) + (neg (suc m')) * n
  end


*-distrib-+ : {m n p : Int} -> (m + n) * p == (m * p) + (n * p)
*-distrib-+ {zero-int} = refl
*-distrib-+ {pos zero} {n} {p} = 
  begin 
    (pos zero + n) * p
  ==<>
    (add1 n) * p
  ==< add1-extract-* {n} >
    p + (n * p)
  ==< +-left (sym (+-right-zero {p}))  >
    (p + zero-int) + (n * p)
  ==<>
    (pos zero * p) + (n * p)
  end
*-distrib-+ {neg zero} {n} {p} =
  begin 
    (neg zero + n) * p
  ==<>
    (sub1 n) * p
  ==< sub1-extract-* {n} >
    - p + (n * p)
  ==< +-left (cong minus (sym (+-right-zero {p}))) >
    - (p + zero-int) + (n * p)
  ==<>
    (neg zero * p) + (n * p)
  end
*-distrib-+ {pos (suc m')} {n} {p} =
  begin
    (pos (suc m') + n) * p
  ==<>
    add1 (pos m' + n) * p
  ==< add1-extract-* {pos m' + n} >
    p + ((pos m') + n) * p
  ==< +-right {p} (*-distrib-+ {pos m'}) >
    p + ((pos m') * p + n * p)
  ==< sym (+-assoc {p}) >
    (p + (pos m') * p) + n * p
  ==<>
    (pos (suc m') * p) + (n * p)
  end 
*-distrib-+ {neg (suc m')} {n} {p} =
  begin
    (neg (suc m') + n) * p
  ==<>
    sub1 (neg m' + n) * p
  ==< sub1-extract-* {neg m' + n} >
    - p + ((neg m') + n) * p
  ==< +-right { - p} (*-distrib-+ {neg m'}) >
    - p + ((neg m') * p + n * p)
  ==< sym (+-assoc { - p}) >
    (- p + (neg m') * p) + n * p
  ==< +-left (sym (minus-distrib-+ {p})) >
    - (p + (pos m') * p) + n * p
  ==<>
    (neg (suc m') * p) + (n * p)
  end 

*-assoc : {m n o : Int} -> (m * n) * o == m * (n * o)
*-assoc {zero-int} = refl
*-assoc {pos zero} {n} {o} = 
  begin
    ((pos zero) * n) * o
  ==<>
    (n + zero-int) * o
  ==< *-left (+-right-zero {n}) >
    n * o
  ==< sym +-right-zero  >
    (n * o) + zero-int
  ==<>
    (pos zero) * (n * o)
  end
*-assoc {neg zero} {n} {o} =
  begin
    ((neg zero) * n) * o
  ==<>
    - (n + zero-int) * o
  ==< *-left (cong minus (+-right-zero {n})) >
    - n * o
  ==< minus-extract-left {n} >
    - (n * o)
  ==< sym (cong minus (+-right-zero {n * o})) >
    - ((n * o) + zero-int)
  ==<>
    (neg zero) * (n * o)
  end
*-assoc {pos (suc m')} {n} {o} =
  begin
    (pos (suc m') * n) * o
  ==<>
    (n + pos m' * n) * o
  ==< *-distrib-+ {n} >
    n * o + (pos m' * n) * o
  ==< +-right {n * o} (*-assoc {pos m'} {n} {o}) >
    n * o + pos m' * (n * o)
  ==<>
    pos (suc m') * (n * o)
  end
*-assoc {neg (suc m')} {n} {o} =
  begin
    (neg (suc m') * n) * o
  ==<>
    - (n + pos m' * n) * o
  ==< minus-extract-left {n + pos m' * n}>
    - ((n + pos m' * n) * o)
  ==< cong minus (*-distrib-+ {n}) >
    - (n * o + (pos m' * n) * o)
  ==< cong minus (+-right {n * o} (*-assoc {pos m'} {n} {o})) >
    - (n * o + pos m' * (n * o))
  ==<>
    neg (suc m') * (n * o)
  end


*-commute : {m n : Int} -> m * n == n * m
*-commute {zero-int} {n} = sym (*-right-zero {n})
*-commute {pos zero} {n} =
  begin
    pos zero * n
  ==< +-right-zero {n} >
    n
  ==< sym *-right-one >
    n * pos zero
  end
*-commute {neg zero} {n} =
  begin
    neg zero * n
  ==< cong minus (+-right-zero {n}) >
    - n
  ==< sym (*-right-negative-one {n}) >
    n * neg zero
  end
*-commute {pos (suc m')} {n} = 
  begin
    pos (suc m') * n
  ==<>
    n + pos m' * n
  ==< +-right {n} (*-commute {pos m'} {n}) >
    n + n * pos m'
  ==< sym (add1-extract-*-right {n}) >
    n * pos (suc m')
  end
*-commute {neg (suc m')} {n} =
  begin
    neg (suc m') * n
  ==<>
    - (n + pos m' * n)
  ==< minus-distrib-+ {n} >
    - n + neg m' * n
  ==< +-right { - n} (*-commute {neg m'} {n}) >
    - n + n * neg m'
  ==< sym (sub1-extract-*-right {n}) >
    n * neg (suc m')
  end

-- infix 20 _div_
data _div_ : Int -> Int -> Set where
 div-exist : (a : Int) -> (b : Int) -> (c : Int) -> (c * a == b) -> a div b


==-div-right : {d a b : Int} -> a == b -> d div a -> d div b
==-div-right refl div = div

div-refl : {n : Int} -> n div n
div-refl {n} = (div-exist n n (pos zero) (+-right-zero {n}))

div-trans : {d m n : Int} -> d div m -> m div n -> d div n
div-trans (div-exist d m a refl) (div-exist m n b refl) = 
  div-exist d n (b * a) (*-assoc {b})

div-mult : {d n a : Int} -> d div n -> (a * d) div (a * n)
div-mult {d} {n} {a} (div-exist d n c refl) =
  div-exist (a * d) (a * n) c 
  (begin
     c * (a * d)
   ==< sym (*-assoc {c}) >
     (c * a) * d
   ==< *-left (*-commute {c} {a}) >
     (a * c) * d
   ==< *-assoc {a}  >
     a * (c * d)
   ==<>
     a * n
   end)

div-negate : {d a : Int} -> d div a -> d div (- a)
div-negate (div-exist d a d-div-a refl) =
  (div-exist d (- a) (- d-div-a) (minus-extract-left {d-div-a}))


div-sum : {d a b : Int} -> d div a -> d div b -> d div (a + b)
div-sum (div-exist d a d-div-a refl) (div-exist d b d-div-b refl) =
  div-exist d (a + b) (d-div-a + d-div-b) (*-distrib-+ {d-div-a}) 

div-linear : {d a b : Int} -> d div a -> d div b -> {m n : Int} -> d div (m * a + n * b)
div-linear (div-exist d a d-div-a refl) (div-exist d b d-div-b refl) {m} {n} =
  div-exist d (m * a + n * b) (m * d-div-a + n * d-div-b)
  (begin
     (m * d-div-a + n * d-div-b) * d
   ==< *-distrib-+ {m * d-div-a} >
     (m * d-div-a) * d + (n * d-div-b) * d
   ==< +-left (*-assoc {m}) >
     m * a + (n * d-div-b) * d
   ==< +-right {m * a} (*-assoc {n}) >
     m * a + n * b 
   end)
 
div-one : {n : Int} -> ((int 1) div n)
div-one {n} = div-exist (int 1) n n (*-right-one {n})

div-zero : {n : Int} -> (n div zero-int)
div-zero {n} = div-exist n zero-int zero-int refl 

data GCD : Int -> Int -> Int -> Set where
 gcd : (a : Int) -> (b : Int) -> (d : Int) -> (d div a) -> (d div b)
       -> ((x : Int) -> x div a -> x div b -> x div d) -> GCD a b d

gcd-refl : {n : Int} -> GCD n n n
gcd-refl {n} = gcd n n n div-refl div-refl (\ _ _ d -> d)

gcd-sym : {a b d : Int} -> GCD a b d -> GCD b a d
gcd-sym (gcd a b d div-a div-b f) = (gcd b a d div-b div-a (\ x xb xa -> f x xa xb))

gcd-zero : {a : Int} -> GCD a zero-int a
gcd-zero {a} = (gcd a zero-int a div-refl div-zero (\ x xa xz -> xa))

gcd-pos->neg : {a : Nat} {b d : Int} -> GCD (pos a) b d -> GCD (neg a) b d
gcd-pos->neg (gcd (pos a) b d d-div-a d-div-b f) =
  (gcd (neg a) b d (div-negate d-div-a) d-div-b (\ x xa xb -> f x (div-negate xa) xb))

gcd-negate : {a b d : Int} -> GCD a b d -> GCD (- a) b d
gcd-negate (gcd a b d d-div-a d-div-b f) =
  (gcd (- a) b d (div-negate d-div-a) d-div-b g)
  where 
  g : (x : Int) -> x div (- a) -> x div b -> x div d
  g x xa xb = f x rewritten-xa xb
    where
    xa2 : x div (- (- a))
    xa2 = (div-negate xa)
    rewritten-xa : x div a
    rewritten-xa rewrite sym (minus-double-inverse {a}) = xa2


data LinearCombination : Int -> Int -> Int -> Set where
 linear-combo : (a : Int) -> (b : Int) -> (d : Int) -> (x : Int) -> (y : Int)
   -> {x * a + y * b == d}
   -> LinearCombination a b d

linear-combo->gcd : {a b d : Int} -> LinearCombination a b d -> d div a -> d div b -> GCD a b d
linear-combo->gcd (linear-combo a b d x y {refl}) da db = 
  (gcd a b d da db (\ z za zb -> div-linear za zb {x} {y}))

data exists : {A : Set} -> (B : A -> Set) -> Set where
 existence : {A : Set} -> {B : A -> Set} -> (x : A) -> (y : B x) -> exists B

data CompareNat3 : Nat -> Nat -> Set where
  compare3-= : {m n : Nat} -> m == n -> CompareNat3 m n
  compare3-< : {a m n : Nat} 
    -> (pos a) + (pos m) == (pos n) 
    -> suc (a +' m) ≤ (m +' n)
    -> CompareNat3 m n
  compare3-> : {a m n : Nat} 
    -> (pos a) + (pos n) == (pos m) 
    -> suc (a +' n) ≤ (m +' n)
    -> CompareNat3 m n
decide-compare3 : (m : Nat) -> (n : Nat) -> CompareNat3 m n
decide-compare3 zero zero = compare3-= refl
decide-compare3 zero (suc n) = compare3-< {n} (+-commute {pos n}) ≤-proof
  where 
  ≤-proof : (suc n +' zero) ≤ suc n
  ≤-proof rewrite (+'-right-zero {suc n}) = id-≤
decide-compare3 (suc m) zero = compare3-> {m} (+-commute {pos m}) id-≤
decide-compare3 (suc m) (suc n) = fix (decide-compare3 m n)
  where fix : CompareNat3 m n -> CompareNat3 (suc m) (suc n)
        fix (compare3-= refl) = (compare3-= refl) 
        fix (compare3-< {a} pr rec-≤) =
          compare3-< {a} (add1-extract-right {pos a} >=> cong add1 pr) ≤-proof
          where 
          ≤-proof : (suc a +' suc m) ≤ (suc m +' suc n)
          ≤-proof rewrite (+'-right-suc {a} {m}) | (+'-right-suc {m} {n}) = 
            inc-≤ (suc-≤ rec-≤)
        fix (compare3-> {a} pr rec-≤) = 
          compare3-> {a} (add1-extract-right {pos a} >=> cong add1 pr) ≤-proof
          where 
          ≤-proof : (suc a +' suc n) ≤ (suc m +' suc n)
          ≤-proof rewrite (+'-right-suc {a} {n}) | (+'-right-suc {m} {n}) = 
            inc-≤ (suc-≤ rec-≤)



eulers-helper : (m : Nat) -> (n : Nat) -> 
                {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} -> 
                GCD (pos a) (pos m) d 
                -> GCD (pos m) (pos n) d
eulers-helper m n {a} pr (gcd _ (pos m) d d-div-a' d-div-m' f) =
  gcd (pos m) (pos n) d d-div-m' div-proof rec-proof
  where
  div-proof : d div (pos n)
  div-proof = ==-div-right pr (div-sum d-div-a' d-div-m') 
  rec-proof : (x : Int) -> x div (pos m) -> x div (pos n) -> x div d
  rec-proof x x-div-m' x-div-n' = f x x-div-a' x-div-m'
    where
    x-div-mn : x div (neg m + pos n)
    x-div-mn = div-sum (div-negate x-div-m') x-div-n'
    mn==a : neg m + pos n == pos a
    mn==a = 
      begin
        neg m + pos n
      ==< +-right {neg m} (sym pr) >
        neg m + (pos a + pos m)
      ==< +-right {neg m} (+-commute {pos a}) >
        neg m + (pos m + pos a)
      ==< sym (+-assoc {neg m}) >
        (neg m + pos m) + pos a
      ==< +-left (add-minus-zero {neg m}) >
        pos a
      end 
    x-div-a' : x div (pos a)
    x-div-a' = ==-div-right mn==a x-div-mn
      
pos-eulers-algo' : (b : Nat) -> (m : Nat) -> (n : Nat)
  -> (suc (m +' n)) ≤ b
  -> exists (GCD (pos m) (pos n))
pos-eulers-algo' (suc b) m n (suc-≤ ≤) = pos-eulers-algo' b m n ≤
pos-eulers-algo' (suc b) m n size-pr = split (decide-compare3 m n)
  where
  split : CompareNat3 m n -> exists (GCD (pos m) (pos n))
  split (compare3-= refl) = existence (pos m) gcd-refl
  split (compare3-< {a} pr rec-size-pr) = handle (pos-eulers-algo' b a m new-size-pr)
    where
    handle : (exists (GCD (pos a) (pos m))) -> (exists (GCD (pos m) (pos n)))
    handle (existence d gc) = (existence d (eulers-helper m n {a} pr {d} gc))
    new-size-pr : (suc (a +' m)) ≤ b
    new-size-pr = trans-≤ rec-size-pr (dec-≤ size-pr)
  split (compare3-> {a} pr rec-size-pr) = handle (pos-eulers-algo' b a n new-size-pr)
    where
    handle : (exists (GCD (pos a) (pos n))) -> (exists (GCD (pos m) (pos n)))
    handle (existence d gc) = (existence d (gcd-sym (eulers-helper n m {a} pr {d} gc)))
    new-size-pr : (suc (a +' n)) ≤ b
    new-size-pr = trans-≤ rec-size-pr (dec-≤ size-pr)
pos-eulers-algo' zero m n ()

pos-eulers-algo : (m : Nat) -> (n : Nat) -> exists (GCD (pos m) (pos n))
pos-eulers-algo m n = pos-eulers-algo' (suc (m +' n)) m n id-≤ 

eulers-algo : (m : Int) -> (n : Int) -> exists (GCD m n)
eulers-algo zero-int zero-int = existence zero-int gcd-refl
eulers-algo zero-int n = existence n (gcd-sym gcd-zero)
eulers-algo m zero-int = existence m gcd-zero
eulers-algo (pos m) (pos n) = pos-eulers-algo m n
eulers-algo (neg m) (pos n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (GCD (pos m) (pos n)) -> exists (GCD (neg m) (pos n))
  handle (existence d pr) = existence d (gcd-negate pr)
eulers-algo (pos m) (neg n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (GCD (pos m) (pos n)) -> exists (GCD (pos m) (neg n))
  handle (existence d pr) = existence d (gcd-sym (gcd-negate (gcd-sym pr)))
eulers-algo (neg m) (neg n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (GCD (pos m) (pos n)) -> exists (GCD (neg m) (neg n))
  handle (existence d pr) = existence d (gcd-sym (gcd-negate (gcd-sym (gcd-negate pr))))



ex1-1 : {a b c d : Int} -> GCD a b (int 1) -> c div a -> d div b -> GCD c d (int 1)
ex1-1 {a} {b} {c} {d} (gcd a b _ _ _ gcd-f) c-div-a d-div-b = 
  gcd c d (int 1) div-one div-one 
  (\x x-div-c x-div-d -> 
    (gcd-f x (div-trans x-div-c c-div-a) (div-trans x-div-d d-div-b)))

ex1-2 : {a b c : Int} -> GCD a b (int 1) -> GCD a c (int 1) -> GCD a (b * c) (int 1)
ex1-2 (gcd a b _ _ _ _) (gcd a c _ _ _ _)  =
  linear-combo->gcd lc div-one div-one
  where
  lc : LinearCombination a (b * c) (int 1)
  lc = ?



-- 
-- data PropEquiv : (A B : Set) -> Set where
--  prop-equiv : {A B : Set} -> (A -> B) -> (B -> A) -> PropEquiv A B
-- 
-- ≤'<->≤ : {m n : Nat} -> PropEquiv (m ≤' n) (m ≤ n)
-- ≤'<->≤  = prop-equiv ≤'->≤ ≤->≤'
