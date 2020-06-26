{-# OPTIONS --cubical --safe --exact-split #-}

module div where

open import abs
open import base
open import equality
open import hlevel
open import int
open import nat
open import relation

-- infix 20 _div_
data _div_ : Int -> Int -> Set where
 div-exists : (a : Int) -> (b : Int) -> (c : Int) -> (c * a == b) -> a div b

data _div'_ : Nat -> Nat -> Set where
 div'-exists : (a : Nat) -> (b : Nat) -> (c : Nat) -> (c *' a == b) -> a div' b

div->div' : {d n : Int} -> d div n -> (abs' d) div' (abs' n)
div->div' (div-exists d n x pr) =
  (div'-exists (abs' d) (abs' n) (abs' x) (sym (abs'-inject-* {x} {d}) >=> (cong abs' pr)))

div'->div : {d n : Nat} -> d div' n -> (int d) div (int n)
div'->div (div'-exists d n x pr) =
  (div-exists (int d) (int n) (int x) (sym (int-inject-*' {x} {d}) >=> (cong int pr)))


div-refl : {n : Int} -> n div n
div-refl {n} = (div-exists n n (int 1) (+-right-zero {n}))

div'-refl : {n : Nat} -> n div' n
div'-refl {n} = (div'-exists n n 1 (+'-right-zero {n}))

div-trans : {d m n : Int} -> d div m -> m div n -> d div n
div-trans (div-exists d m a a*d=m) (div-exists m n b b*m=n) =
  div-exists d n (b * a) ((*-assoc {b} {a} {d}) >=> (*-right {b} a*d=m) >=> b*m=n)

div'-trans : {d m n : Nat} -> d div' m -> m div' n -> d div' n
div'-trans (div'-exists d m a a*d=m) (div'-exists m n b b*m=n) =
  div'-exists d n (b *' a) ((*'-assoc {b} {a} {d}) >=> (*'-right {b} a*d=m) >=> b*m=n)

div-mult : {d n : Int} -> d div n -> (a : Int) -> d div (a * n)
div-mult {d} {n} (div-exists d n c pr) a =
  div-exists d (a * n) (a * c) (*-assoc {a} >=> *-right {a} pr)

div-negate : {d a : Int} -> d div a -> d div (- a)
div-negate (div-exists d a d-div-a pr) =
  (div-exists d (- a) (- d-div-a) ((minus-extract-left {d-div-a}) >=> (cong minus pr)))
div-negate-left : {d a : Int} -> d div a -> (- d) div a
div-negate-left (div-exists d a d-div-a pr) =
  (div-exists (- d) a (- d-div-a)
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
    ==< pr >
      a
    end))

div-abs-right : {d a : Int} -> d div a -> d div (abs a)
div-abs-right {d} {zero-int} div-a = div-a
div-abs-right {d} {pos _} div-a = div-a
div-abs-right {d} {neg _} div-a = div-negate div-a

div-abs-left : {d a : Int} -> d div a -> (abs d) div a
div-abs-left {zero-int} div-a = div-a
div-abs-left {pos _} div-a = div-a
div-abs-left {neg _} div-a = div-negate-left div-a

div'->≤ : {d a : Nat} -> d div' a -> {Pos' a} -> d ≤ a
div'->≤ (div'-exists d a (suc x) sx*d=a) = ≤'->≤ (x *' d , sx*d=a)
div'->≤ (div'-exists d (suc _) zero pr) = zero-suc-absurd pr

div->≤ : {d a : Int} -> d div a -> {Pos a} -> abs' d ≤ abs' a
div->≤ {d} {pos _} da = div'->≤ (div->div' da)


div-zero->zero : {n : Int} -> (int 0) div n -> n == (int 0)
div-zero->zero (div-exists zero-int n d pr) = (sym pr) >=> (*-commute {d} {zero-int})

div'-zero->zero : {n : Nat} -> 0 div' n -> n == 0
div'-zero->zero (div'-exists zero n d pr) = (sym pr) >=> (*'-commute {d} {zero})

div'-pos->pos : {d n : Nat} -> d div' n -> Pos' n -> Pos' d
div'-pos->pos div1@(div'-exists zero n x pr) n-pos =
  (transport (\i -> (Pos' (div'-zero->zero div1 i))) n-pos)
div'-pos->pos (div'-exists (suc _) n x pr) n-pos = tt

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
abs-one-implies-unit {zero-int} pr = zero-suc-absurd pr
abs-one-implies-unit {pos zero} _ = tt
abs-one-implies-unit {pos (suc _)} pr = zero-suc-absurd (suc-injective (sym pr))
abs-one-implies-unit {neg zero} _ = tt
abs-one-implies-unit {neg (suc _)} pr = zero-suc-absurd (suc-injective (sym pr))


*'-one-implies-one : {m n : Nat} -> m *' n == 1 -> n == 1
*'-one-implies-one {zero} {_} pr = zero-suc-absurd pr
*'-one-implies-one {suc m} {zero} pr = *'-one-implies-one {m} {zero} pr
*'-one-implies-one {suc zero} {suc zero} _ = refl
*'-one-implies-one {suc zero} {suc (suc n)} pr = zero-suc-absurd (sym (suc-injective pr))
*'-one-implies-one {suc (suc m)} {suc (suc n)} pr = zero-suc-absurd (sym (suc-injective pr))
*'-one-implies-one {suc (suc m)} {suc zero} pr = zero-suc-absurd (sym (suc-injective pr))


*-one-implies-unit : {m n : Int} -> m * n == (int 1) -> Unit n
*-one-implies-unit {m} {n} pr = (abs-one-implies-unit abs-pr)
  where
  pr1 : abs' m *' abs' n == 1
  pr1 = (sym (abs'-inject-* {m} {n})) >=> (cong abs' pr)
  abs-pr : (abs' n) == 1
  abs-pr = *'-one-implies-one {abs' m} {abs' n} pr1


div'-antisym : {d1 d2 : Nat} -> d1 div' d2 -> d2 div' d1 -> d1 == d2
div'-antisym {zero}   {zero}   div1 div2 = refl
div'-antisym {suc d1} {suc d2} div1 div2 = ≤-antisym (div'->≤ div1) (div'->≤ div2)
div'-antisym {zero}   {suc d2} div1 div2 = zero-suc-absurd (sym (div'-zero->zero div1))
div'-antisym {suc d1} {zero}   div1 div2 = zero-suc-absurd (sym (div'-zero->zero div2))


div-same-abs : {d1 d2 : Int} -> d1 div d2 -> d2 div d1 -> (abs d1) == (abs d2)
div-same-abs {zero-int} {_} div1 _ = (sym (cong abs (div-zero->zero div1)))
div-same-abs {pos _} {zero-int} _ div2 = (cong abs (div-zero->zero div2))
div-same-abs {neg _} {zero-int} _ div2 = (cong abs (div-zero->zero div2))
div-same-abs {pos _} {pos _} (div-exists d1 d2 x pr1) (div-exists d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten = (\i -> x * pr2 i) >=> pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {pos _} {neg _} (div-exists _ _  x pr1) (div-exists d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten = (\i -> x * pr2 i) >=> pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {neg _} {pos _} (div-exists _ _  x pr1) (div-exists d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten = (\i -> x * pr2 i) >=> pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))
div-same-abs {neg _} {neg _} (div-exists _ _  x pr1) (div-exists d2 d1 y pr2) = proof
 where
 rewritten : x * (y * d2) == d2
 rewritten = (\i -> x * pr2 i) >=> pr1
 unit : Unit y
 unit = *-one-implies-unit {x} {y} (*-left-id tt (*-assoc {x} {y} {d2} >=> rewritten))
 proof : abs d1 == abs d2
 proof = sym ((sym (*-unit-abs {y} {d2} unit)) >=> (cong abs pr2))

div-sum : {d a b : Int} -> d div a -> d div b -> d div (a + b)
div-sum (div-exists d a d-div-a pa) (div-exists d b d-div-b pb) =
  div-exists d (a + b) (d-div-a + d-div-b) ((*-distrib-+ {d-div-a}) >=> (+-left pa) >=> (+-right {a} pb))

div-linear : {d a b : Int} -> d div a -> d div b -> {m n : Int} -> d div (m * a + n * b)
div-linear (div-exists d a d-div-a pa) (div-exists d b d-div-b pb) {m} {n} =
  div-exists d (m * a + n * b) (m * d-div-a + n * d-div-b)
  (begin
     (m * d-div-a + n * d-div-b) * d
   ==< *-distrib-+ {m * d-div-a} >
     (m * d-div-a) * d + (n * d-div-b) * d
   ==< +-left (*-assoc {m}) >
     m * (d-div-a * d) + (n * d-div-b) * d
   ==< +-left (*-right {m} pa) >
     m * a + (n * d-div-b) * d
   ==< +-right {m * a} (*-assoc {n}) >
     m * a + n * (d-div-b * d)
   ==< +-right {m * a} (*-right {n} pb) >
     m * a + n * b
   end)

div-one : {n : Int} -> ((int 1) div n)
div-one {n} = div-exists (int 1) n n (*-right-one {n})
div'-one : {n : Nat} -> (1 div' n)
div'-one {n} = div'-exists 1 n n (*'-right-one {n})

div-zero : {n : Int} -> (n div zero-int)
div-zero {n} = div-exists n zero-int zero-int refl
div'-zero : {n : Nat} -> (n div' zero)
div'-zero {n} = div'-exists n zero zero refl

no-small-dividends : {d n : Nat} -> n < d -> n != 0 -> d != 0 -> ¬ (d div' n)
no-small-dividends n<d n!=0 d!=0 (div'-exists d n x pr) with x
... | zero = n!=0 (sym pr)
... | (suc y) = same-≮ n<n
  where
  d≤n : d ≤ n
  d≤n = ≤'->≤ (y *' d , pr)
  n<n : n < n
  n<n = trans-<-≤ n<d d≤n

-- remainder d n a = exists x => a + x * d == n
data Remainder : Nat -> Nat -> Nat -> Set where
  remainder : (d n a x : Nat) -> a < d -> (a +' x *' d == n) -> Remainder d n a

remainder->div : {d n : Nat} -> Remainder d n 0 -> d div' n
remainder->div (remainder d n zero x _ pr) = (div'-exists d n x pr)


div->remainder : {d n : Nat} -> d div' n -> d != 0 -> Remainder d n 0
div->remainder (div'-exists zero n x pr) d!=0 = bot-elim (d!=0 refl)
div->remainder (div'-exists d@(suc d') n x pr) d!=0 =
  (remainder d n 0 x (zero-< {d'}) pr)



private
  -- ModStep d n b x a
  -- d == (suc d')
  -- a + b == d'
  -- n == a + x * d
  data ModStep : Nat -> Nat -> Nat -> Nat -> Nat -> Set where
    mod-base : (d' : Nat) -> ModStep (suc d') 0 d' 0 0
    mod-small-step : {d n b x a : Nat}
                     -> ModStep d n (suc b) x a
                     -> ModStep d (suc n) b x (suc a)
    mod-large-step : {d n b x : Nat}
                     -> ModStep d n zero x b
                     -> ModStep d (suc n) b (suc x) zero

  ¬mod-step-zero : {n b x a : Nat} -> ¬ (ModStep zero n b x a)
  ¬mod-step-zero (mod-small-step step) = ¬mod-step-zero step
  ¬mod-step-zero (mod-large-step step) = ¬mod-step-zero step

  mod-step->remainder : {d n b x a : Nat} -> ModStep d n b x a -> Remainder d n a
  mod-step->remainder {d@(suc d')} {n} {b} {x} {a} step =
    remainder d n a x a<d (eq-step step)
    where
    ab=d' : {n b x a : Nat} -> ModStep d n b x a -> (a +' b) == d'
    ab=d' (mod-base d') = refl
    ab=d' (mod-small-step {d} {n} {b} {x} {a} step) = (sym (+'-right-suc {a} {b})) >=> ab=d' step
    ab=d' (mod-large-step {d} {n} {b} step) = (sym (+'-right-zero {b})) >=> ab=d' step

    a<d : a < d
    a<d = suc-≤ (≤'->≤ (b , (ab=d' step)))

    eq-step : {n b x a : Nat} -> ModStep d n b x a -> a +' x *' d == n
    eq-step (mod-base d') = refl
    eq-step (mod-small-step step) = cong suc (eq-step step)
    eq-step (mod-large-step {d} {n} {a} {x} step) =
      begin
        (suc x) *' d
      ==<>
        suc (d' +' x *' d)
      ==< cong suc (+'-left (sym (ab=d' step))) >
        suc ((a +' 0) +' x *' d)
      ==< cong suc (+'-left (+'-right-zero {a})) >
        suc (a +' x *' d)
      ==< cong suc (eq-step step) >
        (suc n)
      end
  mod-step->remainder {zero} step = bot-elim (¬mod-step-zero step)

  private
    data ModEqProof : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Set where
      mod-eq-proof : {b1 b2 x1 x2 a1 a2 : Nat}
                     -> b1 == b2
                     -> x1 == x2
                     -> a1 == a2
                     -> ModEqProof b1 b2 x1 x2 a1 a2

  unique-mod-step : {d' n b1 b2 x1 x2 a1 a2 : Nat}
                    -> ModStep (suc d') n b1 x1 a1
                    -> ModStep (suc d') n b2 x2 a2 -> ModEqProof b1 b2 x1 x2 a1 a2
  unique-mod-step (mod-base _) (mod-base _) = mod-eq-proof refl refl refl
  unique-mod-step (mod-small-step step1) (mod-small-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof pb px pa) = (mod-eq-proof (suc-injective pb) px (cong suc pa))
  unique-mod-step (mod-large-step step1) (mod-large-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof pb px pa) = (mod-eq-proof pa (cong suc px) pb)
  unique-mod-step (mod-small-step step1) (mod-large-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof p _ _) = zero-suc-absurd (sym p)
  unique-mod-step (mod-large-step step1) (mod-small-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof p _ _) = zero-suc-absurd p


  -- Existential for indices in mod
  data ModOutput : Nat -> Nat -> Set where
    mod-output : {d n b x : Nat} (a : Nat) -> (step : ModStep d n b x a) -> ModOutput d n

  mod : (d : Nat) -> d != 0 -> (n : Nat) -> ModOutput d n
  mod zero d!=0 = bot-elim (d!=0 refl)
  mod d@(suc d') d!=0 n =
    (rec n 0 d' 0 0 (mod-base d') (+'-right-zero {n}))
    where
    rec : (i : Nat) (j : Nat) (b : Nat) (x : Nat) (a : Nat)
          -> ModStep d j b x a
          -> (i +' j == n)
          -> ModOutput d n
    rec zero j b x a step p = transport (\i -> ModOutput d (p i)) (mod-output a step)
    rec (suc i) j zero x acc step p =
      rec i (suc j) acc (suc x) zero (mod-large-step step) (+'-right-suc {i} >=> p)
    rec (suc i) j (suc acc2) x acc1 step p =
      rec i (suc j)  acc2 x (suc acc1) (mod-small-step step) (+'-right-suc {i} >=> p)

exists-remainder : (d : Nat) -> d != 0 -> (n : Nat) -> Σ[ r ∈ Nat ] (Remainder d n r)
exists-remainder d pr n with (mod d pr n)
... | (mod-output a step) = a , (mod-step->remainder step)


private
  data ExistsModStep : Nat -> Nat -> Nat -> Set where
    exists-mod-step : {d n b x a : Nat} (step : ModStep d n b x a) -> ExistsModStep d n a

  data ModStep' : Nat -> Nat -> Nat -> Nat -> Set where
    mod-base' : (d' : Nat) -> ModStep' (suc d') 0 0 0
    mod-small-step' : {d' n x a : Nat}
                      -> ModStep' (suc d') n x a
                      -> ModStep' (suc d') (suc n) x (suc a)
    mod-large-step' : {d' n x : Nat}
                      -> ModStep' (suc d') n x d'
                      -> ModStep' (suc d') (suc n) (suc x) zero


  mod'->mod : {d n x a : Nat} -> ModStep' d n x a -> a < d -> ExistsModStep d n a
  mod'->mod step (b , pr) = exists-mod-step (rec step (sym (+'-commute {b}) >=> pr))
    where
    rec : {d n b x a : Nat} -> ModStep' d n x a -> suc (a +' b) == d -> ModStep d n b x a
    rec {d} (mod-base' d') p =
      transport (\i -> ModStep d 0 (cong pred p (~ i)) 0 0)
                (mod-base d')
    rec {d} {n} {b} {x} {a} (mod-small-step' step) pr =
      mod-small-step (rec step ((+'-right-suc {a} {b}) >=> pr))
    rec {suc d'} {suc n} {b} {suc x} {a} (mod-large-step' step) p =
      mod-large-step (rec tstep path)
      where
      path : (suc b +' 0) == suc d'
      path = cong suc (+'-right-zero {b}) >=> p

      tstep : ModStep' (suc d') n x b
      tstep = transport (\i -> ModStep' (suc d' ) n x (cong pred p (~ i))) step



  remainder->mod-step : {d n a : Nat} -> Remainder d n a -> ExistsModStep d n a
  remainder->mod-step {zero} (remainder _ _ _ _ a<d _) = bot-elim (zero-≮ a<d)
  remainder->mod-step d@{suc d'} (remainder _ n a x a<d pr) =
      (mod'->mod (rec n a x a<d pr) a<d)
    where
    rec : (n a x : Nat) -> a < d -> (a +' x *' d == n) -> ModStep' d n x a
    rec zero zero zero _ refl = (mod-base' d')
    rec (suc n) (suc a) x a<d pr =
      (mod-small-step' (rec n a x (right-suc-< (pred-≤ a<d)) (suc-injective pr)))
    rec (suc n) zero (suc x) _ pr =
      (mod-large-step' (rec n d' x (add1-< d') (suc-injective pr)))

    rec zero    zero    (suc x) a<d pr = zero-suc-absurd (sym pr)
    rec zero    (suc a) (suc x) a<d pr = zero-suc-absurd (sym pr)
    rec zero    (suc a) zero    a<d pr = zero-suc-absurd (sym pr)
    rec (suc n) zero    zero    a<d pr = zero-suc-absurd pr

unique-remainder : {d n a1 a2 : Nat} -> Remainder d n a1 -> Remainder d n a2 -> a1 == a2
unique-remainder {zero} (remainder _ _ _ _ a<d _) = bot-elim (zero-≮ a<d)
unique-remainder {suc _} rem1 rem2
 with (remainder->mod-step rem1) | (remainder->mod-step rem2)
... | (exists-mod-step {d} {n} step1) | (exists-mod-step {d} {n} step2)
 with (unique-mod-step step1 step2)
... | (mod-eq-proof _ _ pr) = pr

remainder->¬div : {d n a : Nat} -> Remainder d n (suc a) -> ¬(d div' n)
remainder->¬div {zero} (remainder _ _ _ _ lt _) = bot-elim (zero-≮ lt)
remainder->¬div {suc _} rem dn =
  (zero-suc-absurd (sym (unique-remainder rem (div->remainder dn (\p -> bot-elim (zero-suc-absurd (sym p)))))))


decide-div : (d n : Nat) -> Dec (d div' n)
decide-div _ zero = yes div'-zero
decide-div zero (suc d) = no f
  where
  f : (x : zero div' (suc d)) -> Bot
  f z-div = zero-suc-absurd (sym (div'-zero->zero z-div))
decide-div d@(suc d') n@(suc _) with (exists-remainder d (\ d=z -> zero-suc-absurd (sym d=z)) n)
... | (zero , rem) = yes (remainder->div rem)
... | ((suc a) , rem) = no (remainder->¬div rem)

isPropDiv' : {d n : Nat} -> {pos : Pos' n} -> isProp (d div' n)
isPropDiv' {pos = n-pos} div1@(div'-exists d n x1 p1) (div'-exists d n x2 p2) i =
  (div'-exists d n (x-p i) (p-p i))
  where
  d-pos : Pos' d
  d-pos = (div'-pos->pos div1 n-pos)

  x-p : x1 == x2
  x-p = (*'-right-injective d-pos (p1 >=> (sym p2)))

  p-p : PathP (\i -> (x-p i) *' d == n) p1 p2
  p-p = isProp->PathP (\i -> (isSetNat _ _)) p1 p2
