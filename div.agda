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

