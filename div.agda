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

remainder->div : {d n : Nat} -> Remainder d n 0 -> d div' n
remainder->div (remainder d n zero x _ pr) = (div'-exist d n x pr)

div->remainder : {d n : Nat} -> d div' n -> d != 0 -> Remainder d n 0
div->remainder (div'-exist zero n x pr) d!=0 = bot-elim (d!=0 refl)
div->remainder (div'-exist d@(suc d') n x pr) d!=0 =
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
    ba=d' : {n b x a : Nat} -> ModStep d n b x a -> (b +' a) == d'
    ba=d' (mod-base d') = +'-right-zero
    ba=d' (mod-small-step {d} {n} {b} {x} {a} step) = (+'-right-suc {b} {a}) >=> ba=d' step
    ba=d' (mod-large-step {d} {n} {b} step) = (+'-right-zero {b}) >=> ba=d' step

    a<d : a < d
    a<d = (inc-≤ (≤-a+'b==c (ba=d' step)))

    eq-step : {n b x a : Nat} -> ModStep d n b x a -> a +' x *' d == n
    eq-step (mod-base d') = refl
    eq-step (mod-small-step step) = cong suc (eq-step step)
    eq-step (mod-large-step {d} {n} {a} {x} step) = 
      begin
        (suc x) *' d
      ==<>
        suc (d' +' x *' d)
      ==< cong suc (+'-left (sym (ba=d' step))) >
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
  ...  | (mod-eq-proof refl refl refl) = (mod-eq-proof refl refl refl)
  unique-mod-step (mod-large-step step1) (mod-large-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof refl refl refl) = (mod-eq-proof refl refl refl)
  unique-mod-step (mod-small-step step1) (mod-large-step step2) 
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof () _ _)
  unique-mod-step (mod-large-step step1) (mod-small-step step2)
    with (unique-mod-step step1 step2)
  ...  | (mod-eq-proof () _ _)


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
    rec zero j b x a step refl = (mod-output a step)
    rec (suc i) j zero x acc step refl =
      rec i (suc j) acc (suc x) zero (mod-large-step step) (+'-right-suc {i})
    rec (suc i) j (suc acc2) x acc1 step refl =
      rec i (suc j)  acc2 x (suc acc1) (mod-small-step step) (+'-right-suc {i})

exists-remainder : (d : Nat) -> d != 0 -> (n : Nat) -> exists (Remainder d n)
exists-remainder d pr n with (mod d pr n)
... | (mod-output a step) = existence a (mod-step->remainder step)
  

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


  a≤b->exists : {a b : Nat} -> a ≤ b -> exists (\ x -> x +' a == b)
  a≤b->exists (zero-≤ {x}) = existence x +'-right-zero
  a≤b->exists (inc-≤ ≤) with (a≤b->exists ≤)
  ... | (existence x refl) = (existence x +'-right-suc)

  mod'->mod : {d n x a : Nat} -> ModStep' d n x a -> a < d -> ExistsModStep d n a
  mod'->mod {_} {_} {_} {a} step a<d with (a≤b->exists a<d) 
  ... | (existence b refl) = exists-mod-step (rec step (sym (+'-commute {b} {suc a})))
    where
    rec : {d n b x a : Nat} -> ModStep' d n x a -> suc (a +' b) == d -> ModStep d n b x a
    rec (mod-base' d') refl = (mod-base d')
    rec {d} {n} {b} {x} {a} (mod-small-step' step) pr = 
      mod-small-step (rec step ((+'-right-suc {a} {b}) >=> pr))
    rec {d} {n} {b} {x} {a} (mod-large-step' step) refl = 
      mod-large-step (rec step (cong suc (+'-right-zero {b})))


  remainder->mod-step : {d n a : Nat} -> Remainder d n a -> ExistsModStep d n a
  remainder->mod-step {zero} (remainder _ _ _ _ () _)
  remainder->mod-step d@{suc d'} (remainder _ n a x a<d pr) =
      (mod'->mod (rec n a x a<d pr) a<d)
    where
    rec : (n a x : Nat) -> a < d -> (a +' x *' d == n) -> ModStep' d n x a
    rec zero zero zero _ refl = (mod-base' d')
    rec (suc n) (suc a) x (inc-≤ a<d) refl =
      (mod-small-step' (rec n a x (suc-< a<d) refl))
    rec (suc n) zero (suc x) (inc-≤ a<d) refl =
      (mod-large-step' (rec n d' x (add1-< d') refl))
  
unique-remainder : {d n a1 a2 : Nat} -> Remainder d n a1 -> Remainder d n a2 -> a1 == a2
unique-remainder {zero} (remainder _ _ _ _ () _) 
unique-remainder {suc _} rem1 rem2
 with (remainder->mod-step rem1) | (remainder->mod-step rem2)
... | (exists-mod-step {d} {n} step1) | (exists-mod-step {d} {n} step2) 
 with (unique-mod-step step1 step2)
... | (mod-eq-proof _ _ pr) = pr


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



