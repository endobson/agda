{-# OPTIONS --cubical --safe --exact-split #-}

module div where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import commutative-monoid
open import equality
open import fin
open import hlevel
open import int
open import integral-domain
open import integral-domain.instances.int
open import nat
open import nat.order
open import order
open import order.instances.nat
open import quotient hiding (remainder)
open import quotient-remainder using
  ( QuotientRemainder
  ; quotient-remainder
  ; isContr-QuotientRemainder
  )
open import relation hiding (acc)
open import ring
open import ring.implementations.int
open import semiring
open import semiring.exponentiation
open import semiring.instances.nat
open import sigma.base

open EqReasoning

_div_ : Int -> Int -> Type₀
a div b = Σ[ c ∈ Int ] (c * a == b)

_div'_ : Nat -> Nat -> Type₀
a div' b = Σ[ c ∈ Nat ] (c *' a == b)

div->div' : {d n : Int} -> d div n -> (abs' d) div' (abs' n)
div->div' {d} (x , pr) =
  (abs' x) , (sym (abs'-inject-* {x} {d}) >=> (cong abs' pr))

div'->div : {d n : Nat} -> d div' n -> (int d) div (int n)
div'->div {d} (x , pr) =
  (int x) , (sym (int-inject-*' {x} {d}) >=> (cong int pr))


div-refl : {n : Int} -> n div n
div-refl  = (int 1) , *-left-one

div'-refl : {n : Nat} -> n div' n
div'-refl = 1 , *'-left-one

div-trans : {d m n : Int} -> d div m -> m div n -> d div n
div-trans {d} (a , a*d=m) (b , b*m=n) =
  (b * a) , (*-assoc >=> (*-right a*d=m) >=> b*m=n)

div'-trans : {d m n : Nat} -> d div' m -> m div' n -> d div' n
div'-trans {d} (a , a*d=m) (b , b*m=n) =
  (b *' a) , ((*'-assoc {b} {a} {d}) >=> (*'-right {b} a*d=m) >=> b*m=n)

div-mult : {d n : Int} -> d div n -> (a : Int) -> d div (a * n)
div-mult (c , pr) a =
  (a * c) , (*-assoc >=> *-right pr)

div-mult' : {d n : Int} -> d div n -> (a : Int) -> d div (n * a)
div-mult' (c , pr) a =
  (a * c) , (*-assoc >=> *-right pr) >=> *-commute

div'-mult : {d n : Nat} -> d div' n -> (a : Nat) -> d div' (a *' n)
div'-mult (c , pr) a =
  (a *' c) , (*'-assoc {a} >=> *'-right {a} pr)

div'-mult' : {d n : Nat} -> d div' n -> (b : Nat) -> d div' (n *' b)
div'-mult' {d} {n} (c , pr) b =
  (b *' c) , (*'-assoc {b} >=> *'-right {b} pr >=> *'-commute {b} {n})

div'-mult-both : {d1 n1 d2 n2 : Nat} -> d1 div' n1 -> d2 div' n2 -> (d1 *' d2) div' (n1 *' n2)
div'-mult-both {d1} {n1} {d2} {n2} (x1 , x1-path) (x2 , x2-path) = x1 *' x2 , path
  where
  path : (x1 *' x2) *' (d1 *' d2) == (n1 *' n2)
  path =
    begin
      (x1 *' x2) *' (d1 *' d2)
    ==< *'-assoc {x1} {x2} >
      x1 *' (x2 *' (d1 *' d2))
    ==< *'-right {x1} (sym (*'-assoc {x2} {d1} {d2})) >
      x1 *' ((x2 *' d1) *' d2)
    ==< *'-right {x1} (*'-left (*'-commute {x2} {d1})) >
      x1 *' ((d1 *' x2) *' d2)
    ==< *'-right {x1} (*'-assoc {d1} {x2} {d2}) >
      x1 *' (d1 *' (x2 *' d2))
    ==< sym (*'-assoc {x1} {d1}) >
      (x1 *' d1) *' (x2 *' d2)
    ==< (\i -> x1-path i *' x2-path i) >
      n1 *' n2
    end

div'-+' : {d n1 n2 : Nat} -> d div' n1 -> d div' n2 -> d div' (n1 +' n2)
div'-+' {d} {n1} {n2} (x1 , path1) (x2 , path2) = (x1 +' x2 , path')
  where
  path' : (x1 +' x2) *' d == n1 +' n2
  path' = *'-distrib-+' {x1} {x2} {d} >=> (\i -> (path1 i) +' (path2 i))

div'-^ℕ : {k1 k2 d : Nat} -> k1 ≤ k2 -> (d ^ℕ k1) div' (d ^ℕ k2)
div'-^ℕ {k1} {k2} {d} (i , path) = (d ^ℕ i , path')
  where
  path' : (d ^ℕ i) *' (d ^ℕ k1) == (d ^ℕ k2)
  path' = sym (^ℕ-distrib-+-left i k1) >=> (cong (d ^ℕ_) path)


div-negate⁺ : {d a : Int} -> d div a -> d div (- a)
div-negate⁺ (c , p) =
  - c , (minus-extract-left >=> cong minus p)

div-negate⁻ : {d a : Int} -> d div (- a) -> d div a
div-negate⁻ (c , p) =
  - c , minus-extract-left >=> cong minus p >=> minus-double-inverse

div-negate-left⁺ : {d a : Int} -> d div a -> (- d) div a
div-negate-left⁺ (c , p) =
  - c , minus-extract-both >=> p

div-negate-left⁻ : {d a : Int} -> (- d) div a -> d div a
div-negate-left⁻ (c , p) =
  - c , minus-extract-left >=> sym minus-extract-right >=> p

div-abs-right : {d a : Int} -> d div a -> d div (abs a)
div-abs-right {d} {zero-int} div-a = div-a
div-abs-right {d} {pos _}    div-a = div-a
div-abs-right {d} {neg _}    div-a = div-negate⁺ div-a

div-abs-left : {d a : Int} -> d div a -> (abs d) div a
div-abs-left {zero-int} div-a = div-a
div-abs-left {pos _}    div-a = div-a
div-abs-left {neg _}    div-a = div-negate-left⁺ div-a

div'->≤ : {d a : Nat} -> d div' a -> {Pos' a} -> d ≤ a
div'->≤ {d} {a}     ((suc x) , sx*d=a) = ≤'->≤ (x *' d , sx*d=a)
div'->≤ {d} {suc _} (zero    , pr    ) = zero-suc-absurd pr

div->≤ : {d a : Int} -> d div a -> {Pos a} -> abs' d ≤ abs' a
div->≤ {a = pos _} da = div'->≤ (div->div' da)


div-zero->zero : {n : Int} -> (int 0) div n -> n == (int 0)
div-zero->zero (d , pr) = (sym pr) >=> *-right-zero

div-non-zero->non-zero : {d n : Int} -> d div n -> NonZero n -> NonZero d
div-non-zero->non-zero {d = pos _} _ _ = (inj-l tt)
div-non-zero->non-zero {d = neg _} _ _ = (inj-r tt)
div-non-zero->non-zero {d = zero-int} d%n n-nz =
  bot-elim (NonZero->¬Zero (subst NonZero (div-zero->zero d%n) n-nz) tt)


div'-zero->zero : {n : Nat} -> 0 div' n -> n == 0
div'-zero->zero (d , pr) = (sym pr) >=> (*'-commute {d} {zero})

div'-one->one : {d : Nat} -> d div' 1 -> d == 1
div'-one->one (x , x*d==1) = *'-only-one-right {x} x*d==1

div'-pos->pos : {d n : Nat} -> d div' n -> Pos' n -> Pos' d
div'-pos->pos {zero} div1 n-pos =
  (transport (\i -> (Pos' (div'-zero->zero div1 i))) n-pos)
div'-pos->pos {suc _} _ _ = tt

div'-pos->pos' : {d n : Nat} -> (d%n : d div' n) -> Pos' n -> Pos' ⟨ d%n ⟩
div'-pos->pos' {d} (x , path) n-pos = div'-pos->pos (d , *'-commute {d} {x} >=> path) n-pos



private
  Unit : (x : Int) -> Type₀
  Unit zero-int = Bot
  Unit (pos zero) = Top
  Unit (pos (suc _)) = Bot
  Unit (neg zero) = Top
  Unit (neg (suc _)) = Bot

*-unit-abs : {m n : Int} -> (Unit m) -> abs (m * n) == abs n
*-unit-abs {pos zero} {n} _ = (cong abs *-left-one)
*-unit-abs {neg zero} {n} _ =
 (cong abs sub1-extract-*)
 >=> (cong (\x -> abs ((- n) + x)) *-left-zero)
 >=> (cong abs +-right-zero)
 >=> (abs-cancel-minus n)

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
div'-antisym {suc d1} {suc d2} div1 div2 = antisym-≤ (div'->≤ div1) (div'->≤ div2)
div'-antisym {zero}   {suc d2} div1 div2 = zero-suc-absurd (sym (div'-zero->zero div1))
div'-antisym {suc d1} {zero}   div1 div2 = zero-suc-absurd (sym (div'-zero->zero div2))


div-same-abs : {d1 d2 : Int} -> d1 div d2 -> d2 div d1 -> (abs d1) == (abs d2)
div-same-abs = step3 _ _
  where
  P : Int -> Int -> Type₀
  P d1 d2 = d1 div d2 -> d2 div d1 -> (abs d1) == (abs d2)

  step1 : ∀ (d1 : Nat) (d2 : Nat) -> P (int d1) (int d2)
  step1 _ _ d1%d2 d2%d1 = cong int (div'-antisym (div->div' d1%d2) (div->div' d2%d1))

  step2 : ∀ (d1 : Nat) (d2 : Int) -> P (int d1) d2
  step2 d1 =
    IntElim-ℕminus-elim
      (step1 d1)
      (\d2 p %₁ %₂ ->
        p (div-negate⁻ %₁) (div-negate-left⁻ %₂) >=>
        (sym (abs-cancel-minus d2)))

  step3 : ∀ (d1 : Int) (d2 : Int) -> P d1 d2
  step3 =
    IntElim-ℕminus-elim
      (\d1 -> step2 d1)
      (\d1 p d2 %₁ %₂ ->
        abs-cancel-minus d1 >=>
        p d2 (div-negate-left⁻ %₁) (div-negate⁻ %₂))


nonneg-unit->one : {n : Int} -> NonNeg n -> Unit n -> n == (int 1)
nonneg-unit->one {n = nonneg (suc zero)} _ _ = refl
nonneg-unit->one {n = neg _} (inj-l ())
nonneg-unit->one {n = neg _} (inj-r ())

div-one->one : {d : Int} -> NonNeg d -> d div (int 1) -> d == (int 1)
div-one->one nn (m , p) = nonneg-unit->one nn (*-one-implies-unit p)


div-sum : {d a b : Int} -> d div a -> d div b -> d div (a + b)
div-sum (d-div-a , _ ) (d-div-b , _ ) .fst = (d-div-a + d-div-b)
div-sum (d-div-a , pa) (d-div-b , pb) .snd =
  *-distrib-+-right >=> +-cong pa pb

div-linear : {d a b : Int} -> d div a -> d div b -> {m n : Int} -> d div (m * a + n * b)
div-linear {d} {a} {b} (d-div-a , pa) (d-div-b , pb) {m} {n} .fst = (m * d-div-a + n * d-div-b)
div-linear {d} {a} {b} (d-div-a , pa) (d-div-b , pb) {m} {n} .snd =
  begin
    (m * d-div-a + n * d-div-b) * d
  ==< *-distrib-+-right >
    (m * d-div-a) * d + (n * d-div-b) * d
  ==< +-left *-assoc >
    m * (d-div-a * d) + (n * d-div-b) * d
  ==< +-left (*-right  pa) >
    m * a + (n * d-div-b) * d
  ==< +-right *-assoc >
    m * a + n * (d-div-b * d)
  ==< +-right (*-right  pb) >
    m * a + n * b
  end

div-+-left : {d a b : Int} -> d div a -> d div (a + b) -> d div b
div-+-left {d} {a} {b} d%a d%ab =
  transport (\i -> d div (path i)) (div-sum (div-negate⁺ d%a) d%ab)
  where
  path : (- a + (a + b)) == b
  path = sym +-assoc >=> (cong (_+ b) (+-commute >=> add-minus-zero {a}))
         >=> +-left-zero

div-+-right : {d a b : Int} -> d div b -> d div (a + b) -> d div a
div-+-right {d} {a} {b} d%b (x , path) = div-+-left d%b (x , path >=> +-commute)

div'-+'-right : {d a b : Nat} -> d div' b -> d div' (a +' b) -> d div' a
div'-+'-right {d} {a} {b} d%b d%ab =
  div->div' (div-+-right {int d} {int a} {int b} (div'->div d%b) d%ab')
  where
  d%ab' : (int d) div ((int a) + (int b))
  d%ab' = (fst (div'->div d%ab)) ,
          (snd (div'->div d%ab)) >=> (CommMonoidʰ.preserves-∙ int-+ʰ a b)

div'-+'-left : {d a b : Nat} -> d div' a -> d div' (a +' b) -> d div' b
div'-+'-left {d} {a} {b} d%a d%ab =
  div->div' (div-+-left {int d} {int a} {int b} (div'->div d%a) d%ab')
  where
  d%ab' : (int d) div ((int a) + (int b))
  d%ab' = (fst (div'->div d%ab)) ,
          (snd (div'->div d%ab)) >=> (CommMonoidʰ.preserves-∙ int-+ʰ a b)




div-one : {n : Int} -> ((int 1) div n)
div-one {n} = n , *-right-one
div'-one : {n : Nat} -> (1 div' n)
div'-one {n} = n , *'-right-one

div-zero : {n : Int} -> (n div zero-int)
div-zero = zero-int , *-left-zero
div'-zero : {n : Nat} -> (n div' zero)
div'-zero = zero , refl

no-small-dividends : {d n : Nat} -> n < d -> n != 0 -> d != 0 -> ¬ (d div' n)
no-small-dividends {d} {n} n<d n!=0 d!=0 (x , pr) with x
... | zero = n!=0 (sym pr)
... | (suc y) = irrefl-< n<n
  where
  d≤n : d ≤ n
  d≤n = ≤'->≤ (y *' d , pr)
  n<n : n < n
  n<n = trans-<-≤ n<d d≤n

-- remainder d n a = exists x => a + x * d == n
data Remainder (d n a : Nat) : Type₀ where
  remainder : (x : Nat) -> a < d -> (a +' x *' d == n) -> Remainder d n a

decide-div : (d n : Nat) -> Dec (d div' n)
decide-div zero zero    = yes div'-zero
decide-div zero (suc d) = no f
  where
  f : (x : zero div' (suc d)) -> Bot
  f z-div = zero-suc-absurd (sym (div'-zero->zero z-div))
decide-div d@(suc d') n = handle (quotient-remainder (d , tt) n)
  where
  handle : QuotientRemainder (d , tt) n -> Dec (d div' n)
  handle (record { q = q ; r = (zero , _)      ; path = path }) =
    yes (q , sym +'-right-zero >=> path )
  handle qr@(record { q = q ; r = (r@(suc _) , _) ; path = path }) = no f
    where
    f : ¬ (d div' n)
    f (q' , p') =
      zero-suc-absurd (cong Fin.i (cong QuotientRemainder.r
        (isContr->isProp isContr-QuotientRemainder qr' qr)))
      where
      qr' : QuotientRemainder (d , tt) n
      qr' = record { q = q' ; r = (zero , zero-<) ; path = +'-right-zero >=> p' }


isPropDiv₁ : {d n : Int} -> (NonZero d) -> isProp (d div n)
isPropDiv₁ {d} {n} nz-d div1@(x1 , p1) (x2 , p2) = ΣProp-path (isSetInt _ _) x-p
  where
  x-p : x1 == x2
  x-p = (*₂-reflects-= (NonZero->!=0 nz-d) (p1 >=> (sym p2)))


isPropDiv : {d n : Int} -> (NonZero n) -> isProp (d div n)
isPropDiv {d} {n} n-nz div1@(x1 , p1) (x2 , p2) = ΣProp-path (isSetInt _ _) x-p
  where
  d-nz : NonZero d
  d-nz = div-non-zero->non-zero div1 n-nz

  x-p : x1 == x2
  x-p = (*₂-reflects-= (NonZero->!=0 d-nz) (p1 >=> (sym p2)))


isPropDiv' : {d : Nat} -> (n : Nat⁺) -> isProp (d div' ⟨ n ⟩)
isPropDiv' {d} (_ , n-pos) div1@(x1 , p1) (x2 , p2) = ΣProp-path (isSetNat _ _) x-p
  where
  d-pos : Pos' d
  d-pos = (div'-pos->pos div1 n-pos)

  x-p : x1 == x2
  x-p = (*'-right-injective (d , d-pos) (p1 >=> (sym p2)))

isPropDiv'₁ : {n : Nat} -> (d : Nat⁺) -> isProp (⟨ d ⟩ div' n)
isPropDiv'₁ {n} (d , d-pos) (x1 , p1) (x2 , p2) = ΣProp-path (isSetNat _ _) x-p
  where
  x-p : x1 == x2
  x-p = (*'-right-injective (d , d-pos) (p1 >=> (sym p2)))


-- Lemmas for Nat⁺

_div⁺_ : Nat⁺ -> Nat⁺ -> Type₀
d div⁺ n = ⟨ d ⟩ div' ⟨ n ⟩

isPropDiv⁺ : {d n : Nat⁺} -> isProp (d div⁺ n)
isPropDiv⁺ {d} {n} = isPropDiv' n

div⁺->multiple⁺ : {d n : Nat⁺} -> d div⁺ n -> Nat⁺
div⁺->multiple⁺ {d' , _} {_ , n-pos} (x , pr) =
  x , div'-pos->pos (d' , *'-commute {d'} {x} >=> pr) n-pos

-- Relate div to quotient
div->quotient : {d : Nat⁺} -> {n : Nat} -> (d%n : ⟨ d ⟩ div' n) -> ⟨ d%n ⟩ == quotient n d
div->quotient {d@(d' , _)} (x , path) =
  (sym quotient-*') >=> (\i -> quotient (path i) d)
