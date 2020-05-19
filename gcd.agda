{-# OPTIONS --cubical #-}

module gcd where

open import base
open import equality
open import abs
open import nat
open import int
open import div
open import prime

data GCD : Int -> Int -> Int -> Set where
 gcd : (a : Int) -> (b : Int) -> (d : Int) -> 
       (NonNeg d) ->
       (d div a) -> (d div b)
       -> ((x : Int) -> x div a -> x div b -> x div d) -> GCD a b d



gcd-refl : {n : Int} -> GCD n n (abs n)
gcd-refl {n} = gcd n n (abs n) tt (div-abs-left div-refl) (div-abs-left div-refl)
 (\ _ _ d -> (div-abs-right d))

gcd-sym : {a b d : Int} -> GCD a b d -> GCD b a d
gcd-sym (gcd a b d non-neg div-a div-b f) =
  (gcd b a d non-neg div-b div-a (\ x xb xa -> f x xa xb))

gcd-zero : {a : Int} -> GCD a zero-int (abs a)
gcd-zero {a} =
  (gcd a zero-int (abs a) tt
      (div-abs-left div-refl) div-zero (\ x xa xz -> (div-abs-right xa)))

gcd-pos->neg : {a : Nat} {b d : Int} -> GCD (pos a) b d -> GCD (neg a) b d
gcd-pos->neg (gcd (pos a) b d non-neg d-div-a d-div-b f) =
  (gcd (neg a) b d non-neg (div-negate d-div-a) d-div-b (\ x xa xb -> f x (div-negate xa) xb))
 
gcd-negate : {a b d : Int} -> GCD a b d -> GCD (- a) b d
gcd-negate (gcd a b d non-neg d-div-a d-div-b f) =
  (gcd (- a) b d non-neg (div-negate d-div-a) d-div-b g)
  where 
  g : (x : Int) -> x div (- a) -> x div b -> x div d
  g x xa xb = f x rewritten-xa xb
    where
    xa2 : x div (- (- a))
    xa2 = (div-negate xa)
    rewritten-xa : x div a
    rewritten-xa rewrite sym (minus-double-inverse {a}) = xa2

gcd-remove-abs : {a b d : Int} -> GCD (abs a) b d -> GCD a b d
gcd-remove-abs {zero-int} g = g
gcd-remove-abs {pos _} g = g
gcd-remove-abs {neg _} g = gcd-negate g


data LinearCombination : Int -> Int -> Int -> Set where
 linear-combo : (a : Int) -> (b : Int) -> (d : Int) -> (x : Int) -> (y : Int)
   -> {x * a + y * b == d}
   -> LinearCombination a b d

linear-combo-refl : {n : Int}  -> LinearCombination n n n
linear-combo-refl {n} = (linear-combo n n n zero-int (pos zero) {+-right-zero {n}})

linear-combo-sym : {a b d : Int} -> LinearCombination a b d -> LinearCombination b a d
linear-combo-sym (linear-combo a b d x y {refl}) =
  (linear-combo b a d y x {+-commute {y * b}})

linear-combo-zero : {n : Int}  -> LinearCombination n zero-int n
linear-combo-zero {n} =
  (linear-combo-sym (linear-combo zero-int n n zero-int (pos zero) {+-right-zero {n}}))

linear-combo-negate : {a b d : Int} -> LinearCombination a b d -> LinearCombination (- a) b d
linear-combo-negate (linear-combo a b d x y {refl}) =
  (linear-combo (- a) b d (- x) y {proof})
  where
    proof : (- x * - a) + y * b ==  d
    proof =
      begin
        - x * - a + y * b
      ==< +-left (minus-extract-left {x}) >
        - (x * - a) + y * b
      ==< +-left (cong minus (minus-extract-right {x})) >
        - (- (x * a)) + y * b
      ==< +-left (minus-double-inverse {x * a}) >
        x * a + y * b
      ==<>
        d
      end 


linear-combo-negate-result : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (- d)
linear-combo-negate-result (linear-combo a b d x y {refl}) =
  (linear-combo a b (- d) (- x) (- y) {proof})
  where
    proof : (- x * a) + (- y * b) == - d
    proof =
      begin
        - x * a + - y * b
      ==< +-left (minus-extract-left {x}) >
        - (x * a) + - y * b
      ==< +-right { - (x * a)} (minus-extract-left {y}) >
        - (x * a) + - (y * b)
      ==< sym (minus-distrib-+ {x * a}) >
        - ((x * a) + (y * b))
      ==<>
        - d
      end 


linear-combo-abs : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (abs d)
linear-combo-abs {a} {b} {zero-int} lc = lc
linear-combo-abs {a} {b} {pos _} lc = lc
linear-combo-abs {a} {b} {neg _} lc = (linear-combo-negate-result lc)


linear-combo->gcd : {a b d : Int} -> LinearCombination a b d -> d div a -> d div b -> GCD a b (abs d)
linear-combo->gcd (linear-combo a b d x y {refl}) da db = 
  (gcd a b (abs d) tt (div-abs-left da) (div-abs-left db)
    (\ z za zb -> (div-abs-right (div-linear za zb {x} {y}))))

data LinearGCD : Int -> Int -> Int -> Set where
 linear-gcd : {a : Int} -> {b : Int} -> {d : Int}
   -> (lc : (LinearCombination a b d))
   -> (gcd : (GCD a b d))
   -> LinearGCD a b d

linear-gcd-sym : {a b d : Int} -> LinearGCD a b d -> LinearGCD b a d
linear-gcd-sym (linear-gcd lc gc) = (linear-gcd (linear-combo-sym lc) (gcd-sym gc))

linear-gcd-negate : {a b d : Int} -> LinearGCD a b d -> LinearGCD (- a) b d
linear-gcd-negate (linear-gcd lc gc) = (linear-gcd (linear-combo-negate lc) (gcd-negate gc))

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
  ≤-proof rewrite (+'-right-zero {suc n}) = same-≤ (suc n)
decide-compare3 (suc m) zero = compare3-> {m} (+-commute {pos m}) (same-≤ (suc (m +' zero)))
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


eulers-helper-gcd : (m : Nat) -> (n : Nat) -> 
                    {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} -> 
                    GCD (pos a) (pos m) d 
                    -> GCD (pos m) (pos n) d
eulers-helper-gcd m n {a} pr (gcd _ (pos m) d non-neg d-div-a' d-div-m' f) =
  gcd (pos m) (pos n) d non-neg d-div-m' div-proof rec-proof
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

eulers-helper-lc : (m : Nat) -> (n : Nat) -> 
                   {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} -> 
                   LinearCombination (pos a) (pos m) d 
                   -> LinearCombination (pos m) (pos n) d
eulers-helper-lc m' n' {a'} add-pr (linear-combo a m d x y {refl}) =
  (linear-combo m n d z x {proof})
  where
  n : Int
  n = pos n'
  z : Int
  z = - x + y
  proof : z * m + x * n == d
  proof =
    begin
       z * m + x * n
    ==< +-commute {z * m} >
       x * n + z * m 
    ==< +-left (*-right {x} (sym add-pr)) >
       x * (a + m) + z * m 
    ==< +-left (*-commute {x}) >
       (a + m) * x + z * m
    ==< +-left (*-distrib-+ {a}) >
       (a * x + m * x) + z * m 
    ==< +-left (+-left (*-commute {a} {x})) > 
       (x * a + m * x) + z * m 
    ==< +-left (+-right {x * a} (*-commute {m} {x})) >
       (x * a + x * m) + z * m 
    ==< +-assoc {x * a} >
       x * a + (x * m + z * m)
    ==< +-right {x * a} (sym (*-distrib-+ {x})) >
       x * a + (x + z) * m
    ==<>
       x * a + (x + (- x + y)) * m
    ==< +-right {x * a} (*-left (sym (+-assoc {x}))) >
       x * a + ((x + - x) + y) * m
    ==< +-right {x * a} (*-left (+-left (add-minus-zero {x}))) >
       x * a + y * m
    ==<>
      d
    end

eulers-helper : (m : Nat) -> (n : Nat) -> 
                {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} -> 
                LinearGCD (pos a) (pos m) d 
                -> LinearGCD (pos m) (pos n) d
eulers-helper m n {a} pr {d} (linear-gcd lc gc) =
  (linear-gcd (eulers-helper-lc m n {a} pr {d} lc)
              (eulers-helper-gcd m n {a} pr {d} gc))

pos-eulers-algo' : (b : Nat) -> (m : Nat) -> (n : Nat)
  -> (m +' n) < b
  -> exists (LinearGCD (pos m) (pos n))
pos-eulers-algo' (suc b) m n size-pr = split (decide-compare3 m n)
  where
  split : CompareNat3 m n -> exists (LinearGCD (pos m) (pos n))
  split (compare3-= refl) = existence (pos m) (linear-gcd linear-combo-refl gcd-refl)
  split (compare3-< {a} pr rec-size-pr) = handle (pos-eulers-algo' b a m new-size-pr)
    where
    handle : (exists (LinearGCD (pos a) (pos m))) -> (exists (LinearGCD (pos m) (pos n)))
    handle (existence d gc) = (existence d (eulers-helper m n {a} pr {d} gc))
    new-size-pr : (a +' m) < b
    new-size-pr = dec-< (trans-≤-< rec-size-pr size-pr)
  split (compare3-> {a} pr rec-size-pr) = handle (pos-eulers-algo' b a n new-size-pr)
    where
    handle : (exists (LinearGCD (pos a) (pos n))) -> (exists (LinearGCD (pos m) (pos n)))
    handle (existence d gc) = (existence d (linear-gcd-sym (eulers-helper n m {a} pr {d} gc)))
    new-size-pr : (a +' n) < b
    new-size-pr = dec-< (trans-≤-< rec-size-pr size-pr)
pos-eulers-algo' zero m n ()


pos-eulers-algo : (m : Nat) -> (n : Nat) -> exists (LinearGCD (pos m) (pos n))
pos-eulers-algo m n = pos-eulers-algo' (suc (m +' n)) m n (add1-< (m +' n))


eulers-algo : (m : Int) -> (n : Int) -> exists (LinearGCD m n)
eulers-algo zero-int zero-int = existence zero-int (linear-gcd linear-combo-refl gcd-refl)
eulers-algo zero-int n = existence (abs n) 
  (linear-gcd-sym (linear-gcd (linear-combo-abs linear-combo-zero) gcd-zero))
eulers-algo m zero-int = existence (abs m) (linear-gcd (linear-combo-abs linear-combo-zero) gcd-zero)
eulers-algo (pos m) (pos n) = pos-eulers-algo m n
eulers-algo (neg m) (pos n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (LinearGCD (pos m) (pos n)) -> exists (LinearGCD (neg m) (pos n))
  handle (existence d pr) = existence d (linear-gcd-negate pr)
eulers-algo (pos m) (neg n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (LinearGCD (pos m) (pos n)) -> exists (LinearGCD (pos m) (neg n))
  handle (existence d pr) = existence d (linear-gcd-sym (linear-gcd-negate (linear-gcd-sym pr)))
eulers-algo (neg m) (neg n) = handle (pos-eulers-algo m n) 
  where
  handle : exists (LinearGCD (pos m) (pos n)) -> exists (LinearGCD (neg m) (neg n))
  handle (existence d pr) = 
    existence d (linear-gcd-sym (linear-gcd-negate (linear-gcd-sym (linear-gcd-negate pr))))

gcd-exists : (m : Int) -> (n : Int) -> exists (GCD m n)
gcd-exists m n with (eulers-algo m n)
...               | (existence d (linear-gcd _ gc)) = existence d gc


non-neg-same-abs : {m n : Int} -> NonNeg m -> NonNeg n -> abs m == abs n -> m == n
non-neg-same-abs {nonneg m} {nonneg n} _ _ eq = eq

gcd-unique : {m n d1 d2 : Int} -> GCD m n d1 -> GCD m n d2 -> d1 == d2
gcd-unique (gcd m n d1 d1-nn d1-div-m d1-div-n d1-f)
           (gcd m n d2 d2-nn d2-div-m d2-div-n d2-f) =
  non-neg-same-abs d1-nn d2-nn (div-same-abs d1-div-d2 d2-div-d1)
  where
  d1-div-d2 : d1 div d2
  d1-div-d2 = (d2-f d1 d1-div-m d1-div-n)
  d2-div-d1 : d2 div d1
  d2-div-d1 = (d1-f d2 d2-div-m d2-div-n)

gcd->linear-combo : {a b d : Int} -> GCD a b d -> LinearCombination a b d
gcd->linear-combo {a} {b} {d} gcd-d = handle (eulers-algo a b)
  where
  handle : exists (LinearGCD a b) -> LinearCombination a b d
  handle (existence d' (linear-gcd lc gcd-d')) rewrite (gcd-unique gcd-d gcd-d') = lc

data GCD' : Nat -> Nat -> Nat -> Set where
 gcd' : (a : Nat) -> (b : Nat) -> (d : Nat) -> 
        (d div' a) -> (d div' b)
        -> ((x : Nat) -> x div' a -> x div' b -> x div' d) -> GCD' a b d

gcd'-zero->id : {b d : Nat} -> GCD' 0 b d -> b == d
gcd'-zero->id (gcd' 0 b d d%0 d%b f) = div'-antisym (f b div'-zero div'-refl) d%b 


gcd'->gcd/nat : {d n a : Nat} -> GCD' d n a -> GCD (int d) (int n) (int a)
gcd'->gcd/nat (gcd' d n a a%d a%n f') =
  (gcd (int d) (int n) (int a) tt (div'->div a%d) (div'->div a%n) f)
  where
  fix : {x : Int} -> {y : Nat} -> x div (int y) -> (abs' x) div' y
  fix {x} {y} x%y = (subst (\ z -> (abs' x) div' z) refl (div->div' x%y))
  f : (x : Int) -> x div (int d) -> x div (int n) -> x div (int a)
  f x@zero-int x%d x%n = div'->div (f' zero (fix x%d) (fix x%n)) 
  f x@(pos x') x%d x%n = div'->div (f' (suc x') (fix x%d) (fix x%n)) 
  f x@(neg x') x%d x%n = div-negate-left (div'->div (f' (suc x') (fix x%d) (fix x%n)))

gcd'->gcd : {d n a : Int} -> {NonNeg a} -> GCD' (abs' d) (abs' n) (abs' a) -> GCD d n a
gcd'->gcd {zero-int} {zero-int} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {zero-int} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {pos _} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {pos _} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {neg _} {zero-int} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {zero-int} {neg _} {pos _} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {pos _} {zero-int} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {zero-int} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {pos _} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {pos _} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {neg _} {zero-int} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {pos _} {neg _} {pos _} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {neg _} {zero-int} {zero-int} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {neg _} {zero-int} {pos _} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {neg _} {pos _} {zero-int} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {neg _} {pos _} {pos _} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {neg _} {neg _} {zero-int} g = (gcd-negate ((gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))))
gcd'->gcd {neg _} {neg _} {pos _} g = (gcd-negate ((gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))))

gcd->gcd' : {d n a : Int} -> GCD d n a -> GCD' (abs' d) (abs' n) (abs' a)
gcd->gcd' (gcd d n a _ a%d a%n f) =
  (gcd' (abs' d) (abs' n) (abs' a) (div->div' a%d) (div->div' a%n) f')
  where
  f' : (x : Nat) -> x div' (abs' d) -> x div' (abs' n) -> x div' (abs' a)
  f' x x%d x%n = res
    where 
    fix : {y : Int} -> x div' (abs' y) -> (int x) div y
    fix {nonneg _} x%y = (div'->div x%y)
    fix {neg _} x%y = (div-negate (div'->div x%y))
    res : x div' (abs' a)
    res = (div->div' (f (int x) (fix x%d) (fix x%n)))

prime-gcd' : (a b : Nat) -> {Pos' a} -> {Pos' b}
             -> ({p : Nat} -> Prime' p -> p div' a -> p div' b -> Bot)
             -> GCD' a b 1
prime-gcd' a@(suc _) b@(suc _) pf = (gcd' a b 1 div'-one div'-one f)
  where
  f : (x : Nat) -> x div' a -> x div' b -> x div' 1
  f zero x%a x%b with (div'-zero->zero x%a)
  ...               | ()
  f (suc zero) _ _ = div'-one
  f x@(suc (suc _)) x%a x%b with (exists-prime-divisor {x} >1)
  ... | existence _ (prime-p , p%x) =
    bot-elim (pf prime-p (div'-trans p%x x%a) (div'-trans p%x x%b))

euclids-lemma : {a b c : Int} -> a div (b * c) -> GCD a b (int 1) -> a div c
euclids-lemma {a} {b} {c} a%bc ab-gcd with (gcd->linear-combo ab-gcd)
... | (linear-combo _ _ _ x y {pr}) = a%c
  where
  c==stuff : c == x * c * a + y * (b * c)
  c==stuff =
    begin
      c
    ==< sym (+-right-zero {c})  >
      (int 1) * c
    ==< *-left (sym pr) >
      (x * a + y * b) * c
    ==< *-distrib-+ {x * a}  >
      x * a * c + y * b * c
    ==< +-left (*-assoc {x}) >
      x * (a * c) + y * b * c
    ==< +-left (*-right {x} (*-commute {a} {c})) >
      x * (c * a) + y * b * c
    ==< sym (+-left (*-assoc {x})) >
      x * c * a + y * b * c
    ==< (+-right {x * c * a} (*-assoc {y})) >
      x * c * a + y * (b * c)
    end 
  a%stuff : a div (x * c * a + y * (b * c))
  a%stuff = div-linear div-refl a%bc {x * c} {y}

  a%c : a div c
  a%c = (subst (\ x -> a div x) (sym c==stuff) a%stuff)

euclids-lemma' : {a b c : Nat} -> a div' (b *' c) -> GCD' a b 1 -> a div' c
euclids-lemma' {a} {b} {c} a%bc ab-gcd = result
  where
  int-a%bc : (int a) div (int b * int c)
  int-a%bc rewrite sym (int-inject-*' {b} {c}) = (div'->div a%bc)
  result : a div' c
  result = (div->div' (euclids-lemma int-a%bc (gcd'->gcd/nat ab-gcd)))


prime->relatively-prime : {p a : Nat} -> Prime' p -> ¬ (p div' a) -> GCD' p a 1
prime->relatively-prime {p} {a} prime-p ¬p%a =
  (gcd' p a 1 div'-one div'-one f)
  where
  f : (x : Nat) -> x div' p -> x div' a -> x div' 1
  f x x%p x%a with (prime-only-divisors prime-p x%p)
  ... | inj-l refl = bot-elim (¬p%a x%a)
  ... | inj-r refl = div'-one

prime-divides-a-factor : {p : Nat} -> Prime' p -> {a b : Nat} 
                         -> p div' (a *' b) -> (p div' a) ⊎ (p div' b)
prime-divides-a-factor {p} prime-p {a} {b} p-div with (decide-div p a)
... | yes p%a = inj-l p%a
... | no ¬p%a = inj-r (euclids-lemma' p-div (prime->relatively-prime prime-p ¬p%a))
