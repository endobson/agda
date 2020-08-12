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

+'-left-injective : {m n p : Nat} -> (m +' n) == (m +' p) -> n == p
+'-left-injective {zero}  path = path
+'-left-injective {suc m} path = +'-left-injective (suc-injective path)

+'-right-injective : {m n p : Nat} -> (n +' m) == (p +' m) -> n == p
+'-right-injective {m} {n} {p} path =
  +'-left-injective (+'-commute {m} {n} ∙∙ path ∙∙ +'-commute {p} {m})

+'-assoc : {m n o : Nat} -> (m +' n) +' o == m +' (n +' o)
+'-assoc {zero} {_} {_} = refl
+'-assoc {suc m} {_} {_} = cong suc (+'-assoc {m})

m+'n==0->m==0 : {m n : Nat} -> m +' n == 0 -> m == 0
m+'n==0->m==0 {0} p = refl
m+'n==0->m==0 {(suc _)} p = bot-elim (zero-suc-absurd (sym p))

-- Properties of -

+'-minus-left : (m : Nat) {n : Nat} -> (m +' n) -' m == n
+'-minus-left zero = refl
+'-minus-left (suc m) = +'-minus-left m

+'-minus-right : {m : Nat} (n : Nat) -> (m +' n) -' n == m
+'-minus-right {m} n = (\i -> +'-commute {m} {n} i -' n) >=> +'-minus-left n

+'-minus-rev : {m : Nat} (n : Nat) -> .(Pos' (m -' n)) -> (m -' n) +' n == m
+'-minus-rev {zero} zero    ()
+'-minus-rev {zero} (suc n) ()
+'-minus-rev {suc m} zero _ = +'-right-zero
+'-minus-rev {suc m} (suc n) p = +'-right-suc >=> cong suc (+'-minus-rev n p)



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

*'-Pos'-Pos' : {m n : Nat} -> .(Pos' m) -> .(Pos' n) -> Pos' (m *' n)
*'-Pos'-Pos' {(suc m)} {(suc n)} _ _ = tt

*'-right-injective : {m : Nat} (n : Nat⁺) {p : Nat} -> (m *' ⟨ n ⟩) == (p *' ⟨ n ⟩) -> m == p
*'-right-injective {zero}    _           {zero}  path = refl
*'-right-injective {zero}    (_ , n-pos) {suc p} path =
  bot-elim (transport (cong Pos' (sym path)) (*'-Pos'-Pos' {suc p} tt n-pos))
*'-right-injective {suc m}   (_ , n-pos) {zero}  path =
  bot-elim (transport (cong Pos' path) (*'-Pos'-Pos' {suc m} tt n-pos))
*'-right-injective {suc m} n@(_ , _) {suc p} path =
  (cong suc (*'-right-injective n (transport (sym (+'-left-path _)) path)))

*'-left-injective : (m : Nat⁺) {n p : Nat} -> (⟨ m ⟩ *' n) == (⟨ m ⟩ *' p) -> n == p
*'-left-injective m@(m' , _) {n} {p} path =
  *'-right-injective m (*'-commute {n} {m'} ∙∙ path ∙∙ *'-commute {m'} {p})


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

^'-Pos' : {a : Nat} -> .(Pos' a) -> (b : Nat) -> Pos' (a ^' b)
^'-Pos' _ zero = tt
^'-Pos' p (suc n) = *'-Pos'-Pos' p (^'-Pos' p n)


-- Maximum and Minimum

max : Nat -> Nat -> Nat
max 0       n       = n
max (suc m) 0       = (suc m)
max (suc m) (suc n) = suc (max m n)

min : Nat -> Nat -> Nat
min 0       n       = 0
min (suc m) 0       = 0
min (suc m) (suc n) = suc (min m n)

min-max==sum : (a b : Nat) -> (a +' b) == (min a b) +' (max a b)
min-max==sum zero    n       = refl
min-max==sum (suc m) 0       = +'-right-zero
min-max==sum (suc m) (suc n) =
  cong suc (+'-right-suc
            >=> cong suc (min-max==sum m n)
            >=> sym +'-right-suc)


iter : {ℓ : Level} {A : Type ℓ} (n : Nat) (f : A -> A) -> A -> A
iter zero _ a = a
iter (suc n) f a = f (iter n f a)

iter' : {ℓ : Level} {A : Type ℓ} (n : Nat) (f : A -> A) -> A -> A
iter' zero _ a = a
iter' (suc n) f a = (iter' n f (f a))

iter==iter' : {ℓ : Level} {A : Type ℓ} -> Path (Nat -> (A -> A) -> A -> A) iter iter'
iter==iter' {ℓ} {A} i n f a = path-f n f a i
  where
  iter-suc : (n : Nat) (f : A -> A) -> (a : A) -> iter (suc n) f a == iter n f (f a)
  iter-suc zero f a = refl
  iter-suc (suc n) f a i = f (iter-suc n f a i)

  path-f : (n : Nat) -> (f : (A -> A)) -> (a : A) -> iter n f a == iter' n f a
  path-f zero f a i = a
  path-f (suc n) f a = iter-suc n f a >=> (path-f n f (f a))

induction :
  {ℓ : Level}
  {P : Nat -> Type ℓ} ->
  P zero ->
  ({m : Nat} -> P m -> P (suc m)) ->
  (m : Nat) -> P m
induction {P = P} z f zero = z
induction {P = P} z f (suc m) = f (induction {P = P} z f m)


-- Arithmetic on Nat⁺ for simpler signatures

infixl 7 _*⁺_
_*⁺_ : Nat⁺ -> Nat⁺ -> Nat⁺
(a , ap) *⁺ (b , bp) = (a *' b , *'-Pos'-Pos' ap bp)

_^⁺_ : Nat⁺ -> Nat -> Nat⁺
(a , pos-a) ^⁺ b = a ^' b , ^'-Pos' pos-a b

1⁺ : Nat⁺
1⁺ = 1 , tt
