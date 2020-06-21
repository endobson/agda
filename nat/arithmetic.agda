{-# OPTIONS --cubical --safe --exact-split #-}

module nat.arithmetic where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import hlevel
open import isomorphism
open import monoid
open import nat.properties
open import relation

infixl 6 _+'_
_+'_ : Nat -> Nat -> Nat
zero +' n = n
suc m +' n = suc (m +' n)

infixl 6 _-'_
_-'_ : Nat -> Nat -> Nat
m -' zero = m
zero -' (suc n) = zero
(suc m) -' (suc n) = m -' n

pred : (n : Nat) -> Nat
pred n = n -' (suc zero)

+'-right : {m n p : Nat} -> (n == p) -> m +' n == m +' p
+'-right {m} id = cong (\x -> m +' x) id

+'-left : {m n p : Nat} -> (n == p) -> n +' m == p +' m
+'-left {m} id = cong (\x -> x +' m) id

+'-cong : {m n p o : Nat} -> m == p -> n == o -> m +' n == p +' o
+'-cong = cong2 _+'_

+'-right-zero : {m : Nat} -> (m +' zero) == m
+'-right-zero {zero} = refl
+'-right-zero {suc m} = cong suc (+'-right-zero {m})

+'-left-zero : {m : Nat} -> (zero +' m) == m
+'-left-zero {m} = refl

+'-right-suc : {m n : Nat} -> (m +' (suc n)) == suc (m +' n)
+'-right-suc {zero} {n} = refl
+'-right-suc {suc m} {n} = cong suc (+'-right-suc {m} {n})

+'-commute : {m n : Nat} -> (m +' n) == (n +' m)
+'-commute {m} {zero} = +'-right-zero
+'-commute {m} {suc n} = +'-right-suc >=> cong suc (+'-commute {m})

+'-left-path : (m : Nat) {n p : Nat} -> (n == p) == (m +' n == m +' p)
+'-left-path zero    = refl
+'-left-path (suc m) = (+'-left-path m) >=> suc-path

+'-right-path : (m : Nat) {n p : Nat} -> (n == p) == (n +' m == p +' m)
+'-right-path m {n} {p} = +'-left-path m >=> (\j -> +'-commute {m} {n} j == +'-commute {m} {p} j)

+'-assoc : {m n o : Nat} -> (m +' n) +' o == m +' (n +' o)
+'-assoc {zero} {_} {_} = refl
+'-assoc {suc m} {_} {_} = cong suc (+'-assoc {m})

m+'n==0->m==0 : {m n : Nat} -> m +' n == 0 -> m == 0
m+'n==0->m==0 {0} p = refl
m+'n==0->m==0 {(suc _)} p = bot-elim (zero-suc-absurd (sym p))

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

*'-cong : {m n p o : Nat} -> m == p -> n == o -> m *' n == p *' o
*'-cong = cong2 _*'_

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




*'-only-one-left : {m n : Nat} -> m *' n == 1 -> m == 1
*'-only-one-left {m} {zero} p = zero-suc-absurd (sym (*'-right-zero {m}) >=> p)
*'-only-one-left {zero} {(suc _)} p = zero-suc-absurd p
*'-only-one-left {suc zero} {suc zero} _ = refl
*'-only-one-left {suc zero} {suc (suc n)} p = zero-suc-absurd (sym (suc-injective p))
*'-only-one-left {suc (suc m)} {suc n} p =
  zero-suc-absurd ((sym (suc-injective p)) >=> (+'-commute {n}))

*'-only-one-right : {m n : Nat} -> m *' n == 1 -> n == 1
*'-only-one-right {m} {n} p = *'-only-one-left {n} {m} (*'-commute {n} {m} >=> p)


*'-right-injective : {m n p : Nat} (pos : (Pos' n)) -> (m *' n) == (p *' n) -> m == p
*'-right-injective {zero} {suc n} {zero} pos path = refl
*'-right-injective {zero} {suc n} {suc p} pos path = bot-elim (zero-suc-absurd path)
*'-right-injective {suc m} {suc n} {zero} pos path = bot-elim (zero-suc-absurd (sym path))
*'-right-injective {suc m} {suc n} {suc p} pos path =
  (cong suc (*'-right-injective pos (transport (sym (+'-left-path _)) path)))

*'-left-injective : {m n p : Nat} (pos : (Pos' m)) -> (m *' n) == (m *' p) -> n == p
*'-left-injective {m} {n} {p} pos path =
  *'-right-injective pos (*'-commute {n} {m} ∙∙ path ∙∙ *'-commute {m} {p})


*'-distrib-+'-left : {m n p : Nat} -> m *' (n +' p) == (m *' n) +' (m *' p)
*'-distrib-+'-left {m} {n} {p} =
  begin
    m *' (n +' p)
  ==< (*'-commute {m} {n +' p}) >
    (n +' p) *' m
  ==< (*'-distrib-+' {n} {p} {m}) >
    n *' m +' p *' m
  ==< (+'-cong (*'-commute {n} {m}) (*'-commute {p} {m})) >
    (m *' n) +' (m *' p)
  end


_^'_ : Nat -> Nat -> Nat
a ^' zero = 1
a ^' (suc b) = a *' a ^' b

^'-right-one : {a : Nat} -> a ^' 1 == a
^'-right-one = *'-right-one

instance
  NatMonoid+ : Monoid Nat
  NatMonoid+ = record {
    ε = 0;
    _∙_ = _+'_;
    ∙-assoc = \ {m} {n} {o} -> +'-assoc {m} {n} {o};
    ∙-left-ε = +'-left-zero;
    ∙-right-ε = +'-right-zero }

  NatCommMonoid+ : CommMonoid Nat
  NatCommMonoid+ = record
    { ∙-commute = (\ {m} {n} -> +'-commute {m} {n})
    }

  NatMonoid* : Monoid Nat
  NatMonoid* = record {
    ε = 1;
    _∙_ = _*'_;
    ∙-assoc = \ {m} {n} {o} -> *'-assoc {m} {n} {o};
    ∙-left-ε = *'-left-one;
    ∙-right-ε = *'-right-one }

  NatCommMonoid* : CommMonoid Nat
  NatCommMonoid* = record
    { ∙-commute = (\ {m} {n} -> *'-commute {m} {n})
    }

iter : {A : Set} (n : Nat) (f : A -> A) -> A -> A
iter zero _ a = a
iter (suc n) f a = f (iter n f a)

induction :
  {ℓ : Level}
  {P : Nat -> Type ℓ} ->
  P zero ->
  ({m : Nat} -> P m -> P (suc m)) ->
  (m : Nat) -> P m
induction {P = P} z f zero = z
induction {P = P} z f (suc m) = f (induction {P = P} z f m)