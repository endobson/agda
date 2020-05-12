module div where

open import equality
open import abs
open import nat
open import int

-- infix 20 _div_
data _div_ : Int -> Int -> Set where
 div-exist : (a : Int) -> (b : Int) -> (c : Int) -> (c * a == b) -> a div b

data _div'_ : Nat -> Nat -> Set where
 div'-exist : (a : Nat) -> (b : Nat) -> (c : Nat) -> (c *' a == b) -> a div' b

div->div' : {d n : Int} -> d div n -> (abs' d) div' (abs' n)
div->div' (div-exist d n x pr) =
  (div'-exist (abs' d) (abs' n) (abs' x) (sym (abs'-inject-* {x} {d}) >=> (cong abs' pr)))

div'->div : {d n : Nat} -> d div' n -> (int d) div (int n)
div'->div (div'-exist d n x pr) =
  (div-exist (int d) (int n) (int x) (sym (int-inject-*' {x} {d}) >=> (cong int pr)))

 
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
div-negate-left : {d a : Int} -> d div a -> (- d) div a
div-negate-left (div-exist d a d-div-a refl) =
  (div-exist (- d) a (- d-div-a)
   (begin
      (- d-div-a) * (- d)
    ==< minus-extract-left {d-div-a} >
      - (d-div-a * (- d))
    ==< cong minus (*-commute {d-div-a}) >
      - (- d * d-div-a )
    ==< cong minus (minus-extract-left {d}) >
      - - (d * d-div-a)
    ==< minus-double-inverse {d * d-div-a} >
      (d * d-div-a)
    ==< *-commute {d} >
      d-div-a * d
    end))

div-abs-right : {d a : Int} -> d div a -> d div (abs a)
div-abs-right {d} {zero-int} div-a = div-a
div-abs-right {d} {pos _} div-a = div-a
div-abs-right {d} {neg _} div-a = div-negate div-a

div-abs-left : {d a : Int} -> d div a -> (abs d) div a
div-abs-left {zero-int} div-a = div-a
div-abs-left {pos _} div-a = div-a
div-abs-left {neg _} div-a = div-negate-left div-a

div-abs-≤ : {d a : Int} -> {Pos d} -> {Pos a} -> d div a -> abs' d ≤ abs' a
div-abs-≤ {d} {a} {pos-d} (div-exist d a (pos x) refl) = ≤-a+'b==c (sym proof)
  where
  lemma : (z : Nat) -> NonNeg (z *nz d)
  lemma zero = tt
  lemma (suc z) = (Pos->NonNeg (+-Pos-NonNeg pos-d (lemma z)))
  proof : abs' a == abs' (x *nz d) +' abs' d
  proof = 
    begin
      abs' a
    ==<>
      abs' (d + x *nz d)
    ==< cong abs' (+-commute {d}) >
      abs' (x *nz d + d)
    ==< abs'-inject-+ {x *nz d} (lemma x) (Pos->NonNeg pos-d) >
      abs' (x *nz d) +' abs' d
    end
div-abs-≤ {d} {a} {pos-d} {pos-a} (div-exist d a (zero-int) refl) =
  bot-elim pos-a
div-abs-≤ {pos d'} {pos a'} (div-exist _ _ (neg x) pr) =
  bot-elim (subst Neg pr (*-Neg-Pos {neg x} {pos d'} tt tt))



div-zero->zero : {n : Int} -> (int 0) div n -> n == (int 0)
div-zero->zero (div-exist zero-int n d refl) = (*-commute {d} {zero-int})

div'-zero->zero : {n : Nat} -> 0 div' n -> n == 0
div'-zero->zero (div'-exist zero n d refl) = (*'-commute {d} {zero})

Unit : (x : Int) -> Set
Unit zero-int = Bot
Unit (pos zero) = Top
Unit (pos (suc _)) = Bot
Unit (neg zero) = Top
Unit (neg (suc _)) = Bot

*-unit-abs : {m n : Int} -> (Unit m) -> abs (m * n) == abs n
*-unit-abs {pos zero} {n} _ = (cong abs (+-right-zero {n}))
*-unit-abs {neg zero} {n} _ = (cong abs (cong minus (+-right-zero {n}))) >=> (abs-cancel-minus {n})

abs-one-implies-unit : {m : Int} -> abs' m == 1 -> Unit m
abs-one-implies-unit {zero-int} ()
abs-one-implies-unit {pos zero} _ = tt
abs-one-implies-unit {pos (suc _)} ()
abs-one-implies-unit {neg zero} _ = tt
abs-one-implies-unit {neg (suc _)} ()


*'-one-implies-one : {m n : Nat} -> m *' n == 1 -> n == 1
*'-one-implies-one {suc zero} {suc zero} _ = refl
*'-one-implies-one {zero} {_} ()
*'-one-implies-one {suc m} {zero} pr = *'-one-implies-one {m} {zero} pr
*'-one-implies-one {suc zero} {suc (suc n)} ()
*'-one-implies-one {suc (suc m)} {suc (suc n)} ()


*-one-implies-unit : {m n : Int} -> m * n == (int 1) -> Unit n
*-one-implies-unit {m} {n} pr = (abs-one-implies-unit abs-pr)
  where
  pr1 : abs' m *' abs' n == 1
  pr1 = (sym (abs'-inject-* {m} {n})) >=> (cong abs' pr)
  abs-pr : (abs' n) == 1
  abs-pr = *'-one-implies-one {abs' m} {abs' n} pr1



div-same-abs : {d1 d2 : Int} -> d1 div d2 -> d2 div d1 -> (abs d1) == (abs d2)
div-same-abs {zero-int} {_} div1 _ rewrite (div-zero->zero div1) = refl
div-same-abs {_} {zero-int} _ div2 rewrite (div-zero->zero div2) = refl
div-same-abs {pos _} {pos _} (div-exist _ _  x pr1) (div-exist d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten rewrite pr2 = pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {pos _} {neg _} (div-exist _ _  x pr1) (div-exist d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten rewrite pr2 = pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {neg _} {pos _} (div-exist _ _  x pr1) (div-exist d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten rewrite pr2 = pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {neg _} {neg _} (div-exist _ _  x pr1) (div-exist d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten rewrite pr2 = pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))

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

div'-zero : {n : Nat} -> (n div' zero)
div'-zero {n} = div'-exist n zero zero refl 

no-small-dividends : {d n : Nat} -> n < d -> n != 0 -> d != 0 -> ¬ (d div' n)
no-small-dividends n<d n!=0 d!=0 (div'-exist d n x pr) with x 
... | zero = n!=0 (sym pr)
... | (suc y) = absurd-same-< n<n
  where 
  d≤n : d ≤ n
  d≤n = ≤-a+'b==c ((+'-commute {y *' d} {d}) >=> pr)
  n<n : n < n
  n<n = trans-<-≤ n<d d≤n

-- remainder d n a = exists x => a + x * d == n
data Remainder : Nat -> Nat -> Nat -> Set where
  remainder : (d n a x : Nat) -> a < d -> (a +' x *' d == n) -> Remainder d n a

data Remainder' : Nat -> Nat -> Nat -> Set where
  remainder'-base : {d a : Nat} -> a < d -> Remainder' d a a
  remainder'-recur : {d n a : Nat} -> Remainder' d n a -> Remainder' d (d +' n) a

data Remainder2 : Nat -> Nat -> Nat -> Set where
  remainder2-base  : {d : Nat} -> d != 0 -> Remainder2 d 0 0
  remainder2-inc   : {d n a : Nat} -> Remainder2 d n a -> suc a < d
                                   -> Remainder2 d (suc n) (suc a)
  remainder2-reset : {d n a : Nat} -> Remainder2 d n a -> suc a == d 
                                   -> Remainder2 d (suc n) 0


remainder->div : {d n : Nat} -> Remainder d n 0 -> d div' n
remainder->div (remainder d n zero x _ pr) = (div'-exist d n x pr)

div->remainder : {d n : Nat} -> d div' n -> d != 0 -> Remainder d n 0
div->remainder (div'-exist zero n x pr) d!=0 = bot-elim (d!=0 refl)
div->remainder (div'-exist d@(suc d') n x pr) d!=0 =
  (remainder d n 0 x (zero-< d') pr)

remainder'->remainder : {d n a : Nat} -> Remainder' d n a -> Remainder d n a
remainder'->remainder (remainder'-base {d} {a} pr) = (remainder d a a 0 pr +'-right-zero)
remainder'->remainder (remainder'-recur {d} {n} {a} rec) = handle (remainder'->remainder rec)
  where
  handle : (Remainder d n a) -> Remainder d (d +' n) a
  handle (remainder _ _ _ x a<d pr) = (remainder d (d +' n) a (suc x) a<d proof)
    where
    proof : (a +' (suc x) *' d == d +' n)
    proof =
      begin
        a +' (suc x) *' d
      ==<>
        a +' (d +' x *' d)
      ==< sym (+'-assoc {a}) >
        (a +' d) +' x *' d
      ==< +'-left (+'-commute {a}) >
        (d +' a) +' x *' d
      ==< +'-assoc {d} >
        d +' (a +' x *' d)
      ==< +'-right {d} pr >
        d +' n
      end

remainder'-x-deep : (d a x : Nat) -> (a < d) -> Remainder' d (a +' x *' d) a
remainder'-x-deep d a zero a<d rewrite (+'-right-zero {a}) = remainder'-base a<d
remainder'-x-deep d a (suc x) a<d = 
  (subst (\z -> Remainder' d z a) proof (remainder'-recur (remainder'-x-deep d a x a<d)))
  where
  proof : (d +' (a +' x *' d) == a +' (suc x) *' d)
  proof = sym
    (begin
       a +' (suc x) *' d
     ==<>
       a +' (d +' x *' d)
     ==< sym (+'-assoc {a}) >
       (a +' d) +' x *' d
     ==< +'-left (+'-commute {a}) >
       (d +' a) +' x *' d
     ==< +'-assoc {d} >
       d +' (a +' x *' d)
     end)

remainder->remainder' : {d n a : Nat} -> Remainder d n a -> Remainder' d n a
remainder->remainder' (remainder d n a x a<d refl) =
  (remainder'-x-deep d a x a<d)

remainder2-unique : {d n a1 a2 : Nat} -> (Remainder2 d n a1) -> (Remainder2 d n a2) -> a1 == a2
remainder2-unique (remainder2-base _) (remainder2-base _) = refl
remainder2-unique (remainder2-inc rec1 pr1) (remainder2-inc rec2 pr2) =
  (cong suc (remainder2-unique rec1 rec2))
remainder2-unique (remainder2-reset rec1 pr1) (remainder2-reset rec2 pr2) = refl
remainder2-unique (remainder2-inc rec1 pr1) (remainder2-reset rec2 refl)
  rewrite (remainder2-unique rec1 rec2) =
  bot-elim (absurd-same-< pr1)
remainder2-unique (remainder2-reset rec1 refl) (remainder2-inc rec2 pr2)
  rewrite (remainder2-unique rec1 rec2) = 
  bot-elim (absurd-same-< pr2)

remainder2->remainder : {d n a : Nat} -> Remainder2 d n a -> Remainder d n a
remainder2->remainder (remainder2-base {zero} d!=0) = bot-elim (d!=0 refl)
remainder2->remainder (remainder2-base {d@(suc d')} d!=0) =
  (remainder d 0 0 0 (zero-< d') refl)
remainder2->remainder (remainder2-inc rec a<d) with (remainder2->remainder rec)
... | (remainder d n a x _ pr) = (remainder d (suc n) (suc a) x a<d (cong suc pr))
remainder2->remainder (remainder2-reset rec refl) with (remainder2->remainder rec)
... | (remainder d n a x _ refl) = (remainder d (suc n) 0 (suc x) (zero-< a) refl)



-- ModStep d n a b x
-- d == (suc d')
-- a + b == d'
-- n + d' == a + x * d
-- =>
-- n == b + x * d
data ModStep : Nat -> Nat -> Nat -> Nat -> Nat -> Set where
  mod-base : (d' : Nat) -> ModStep (suc d') 0 d' 0 0
  mod-small-step : {d : Nat} -> {n : Nat} -> {a : Nat} -> {b : Nat} -> {x : Nat}
                   -> ModStep d n (suc a) b x
                   -> ModStep d (suc n) a (suc b) x
  mod-large-step : {d : Nat} -> {n : Nat} -> {b : Nat} -> {x : Nat}
                   -> ModStep d n zero b x
                   -> ModStep d (suc n) b zero (suc x)

¬mod-step-zero : {n a b x : Nat} -> ¬ (ModStep zero n a b x)
¬mod-step-zero (mod-small-step step) = ¬mod-step-zero step
¬mod-step-zero (mod-large-step step) = ¬mod-step-zero step

mod-step->remainder : {d n a b x : Nat} -> ModStep d n a b x -> Remainder d n b
mod-step->remainder {d@(suc d')} {n} {a} {b} {x} step = 
  remainder d n b x b<d (eq-step step)
  where
  ab=d' : {n a b x : Nat} -> ModStep d n a b x -> (a +' b) == d'
  ab=d' (mod-base d') = +'-right-zero
  ab=d' (mod-small-step {d} {n} {a} {b} step) = (+'-right-suc {a} {b}) >=> ab=d' step
  ab=d' (mod-large-step {d} {n} {b} step) = (+'-right-zero {b}) >=> ab=d' step

  ba=d' : {n a b x : Nat} -> ModStep d n a b x -> (b +' a) == d'
  ba=d' (mod-base d') = refl
  ba=d' (mod-small-step {d} {n} {a} {b} step) = (sym (+'-right-suc {b} {a})) >=> ba=d' step
  ba=d' (mod-large-step {d} {n} {b} step) = (sym (+'-right-zero {b})) >=> ba=d' step

  a<d : a < d
  a<d = ≤->< (≤-a+'b==c (ba=d' step)) 
  b<d : b < d
  b<d = ≤->< (≤-a+'b==c (ab=d' step)) 

  eq-step : {n a b x : Nat} -> ModStep d n a b x -> b +' x *' d == n
  eq-step (mod-base d') = refl
  eq-step (mod-small-step {d} {n} {a} {b} {x} step) = cong suc (eq-step step)
  eq-step (mod-large-step {d} {n} {b} {x} step) = 
    begin
      (suc x) *' d
    ==<>
      suc (d' +' x *' d)
    ==< cong suc (+'-left (sym (ab=d' step))) >
      suc (b +' x *' d)
    ==< cong suc (eq-step step) >
      (suc n)
    end
mod-step->remainder {zero} step = bot-elim (¬mod-step-zero step)


data ModOutput : Nat -> Nat -> Set where
  mod-output : 
    (d : Nat) ->
    (n : Nat) ->
    (a : Nat) ->
    (b : Nat) ->
    (x : Nat) ->
    (step : ModStep d n a b x) ->
    ModOutput d n

mod : (d : Nat) -> d != 0 -> (n : Nat) -> ModOutput d n
mod zero d!=0 = bot-elim (d!=0 refl)
mod d@(suc d') d!=0 n = 
  (rec n 0 d' 0 0 (mod-base d') (+'-right-zero {n}))
  where
  rec : (i : Nat) (j : Nat) (a : Nat) (b : Nat) (x : Nat)
        -> ModStep d j a b x
        -> (i +' j == n)
        -> ModOutput d n
  rec zero j a b x step refl = (mod-output d j a b x step)
  rec (suc i) j zero acc2 x step refl =
    rec i (suc j) acc2 zero (suc x) (mod-large-step step) (+'-right-suc {i})
  rec (suc i) j (suc acc1) acc2 x step refl =
    rec i (suc j) acc1 (suc acc2) x (mod-small-step step) (+'-right-suc {i})




-- decide-div' : {d n a : Nat} -> Remainder d n a ->  Dec (d div' n)
-- decide-div' {_} {_} {zero} rem = yes (remainder->div rem)
-- decide-div' (remainder d n a@(suc _) x a<d pr) = no handler
--   where
--   handler : d div' n -> Bot
--   handler dn = ?
-- 
-- decide-div : (d n : Nat) -> Dec (d div' n)
-- decide-div _ zero = yes div'-zero
-- decide-div zero (suc d) = no f
--   where 
--   f : (x : zero div' (suc d)) -> Bot
--   f z-div with (div'-zero->zero z-div)
--   ...        | ()
-- decide-div (suc d') (suc n') = ?
--   where
--   small-case : (suc n') < (suc d') -> ¬ ((suc d') div' (suc n'))
--   small-case pr = no-small-dividends pr (\()) (\()) 



