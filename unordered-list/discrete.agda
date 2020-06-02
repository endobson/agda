{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module unordered-list.discrete {ℓ : Level} {A : Type ℓ} (discA : Discrete A) where

open import equality
open import hlevel
open import nat
open import unordered-list.base
open import unordered-list.operations

count : (x : A) -> UList A -> Nat
count x = UListElim.rec isSetNat 0 _::*_ swap*
  where
  _::*_ : (a : A) -> Nat -> Nat
  (a ::* n) with (discA x a)
  ...          | (yes _)     = suc n
  ...          | (no  _)     = n
  swap* : (a1 : A) (a2 : A) -> (n : Nat) -> (a1 ::* (a2 ::* n)) == (a2 ::* (a1 ::* n))
  swap* a1 a2 n with (discA x a1) | (discA x a2)
  ...              | (yes _)      | (yes _)      = refl
  ...              | (yes _)      | (no  _)      = refl
  ...              | (no  _)      | (yes _)      = refl
  ...              | (no  _)      | (no  _)      = refl

count-== : {x : A} {a : A} (as : UList A) -> x == a -> count x (a :: as) == suc (count x as)
count-== {x} {a} as x==a with (discA x a)
...                         | (yes _)     = refl
...                         | (no x!=a)   = bot-elim (x!=a x==a)

count-!= : {x : A} {a : A} (as : UList A) -> x != a -> count x (a :: as) == (count x as)
count-!= {x} {a} as x!=a with (discA x a)
...                         | (yes x==a)  = bot-elim (x!=a x==a)
...                         | (no _)   = refl

remove1 : (x : A) -> UList A -> UList A
remove1 x [] = []
remove1 x (a :: as) with (discA x a)
...                    | (yes _)     = as
...                    | (no  _)     = a :: (remove1 x as)
remove1 x (swap a1 a2 as i) = path i
  where
  path : (remove1 x (a1 :: (a2 :: as))) == (remove1 x (a2 :: (a1 :: as)))
  path with (discA x a1) | (discA x a2)
  ... | (yes p1) | (yes p2) = (\i -> ((sym p2 >=> p1) i) :: as)
  ... | (yes p1) | (no _) = (\i -> a2 :: (inner (~ i)))
    where
    inner : remove1 x (a1 :: as) == as
    inner with (discA x a1)
    ...      | (yes _)      = refl
    ...      | (no ¬p1)     = bot-elim (¬p1 p1)
  ... | (no _) | (yes p2) = (\i -> a1 :: (inner i))
    where
    inner : remove1 x (a2 :: as) == as
    inner with (discA x a2)
    ...      | (yes _)      = refl
    ...      | (no ¬p2)     = bot-elim (¬p2 p2)
  ... | (no ¬p1) | (no ¬p2) = (\i -> a1 :: p i) ∙∙ swap a1 a2 (remove1 x as) ∙∙ (\i -> a2 :: q (~ i))
    where
    p : (remove1 x (a2 :: as)) == a2 :: (remove1 x as)
    p with (discA x a2)
    ...  | (yes p2) = bot-elim (¬p2 p2)
    ...  | (no _)  = refl
    q : (remove1 x (a1 :: as)) == a1 :: (remove1 x as)
    q with (discA x a1)
    ...  | (yes p1) = bot-elim (¬p1 p1)
    ...  | (no _)  = refl
remove1 x (trunc as1 as2 p q i j) =
  (trunc (remove1 x as1) (remove1 x as2) (cong (remove1 x) p) (cong (remove1 x) q) i j)

remove1-== : {x : A} {a : A} (as : UList A) -> (x == a) -> remove1 x (a :: as) == as
remove1-== {x} {a} as x==a with (discA x a)
...                         | (yes _)     = refl
...                         | (no x!=a)   = bot-elim (x!=a x==a)

remove1-!= : {x : A} {a : A} (as : UList A) -> (x != a) -> remove1 x (a :: as) == a :: (remove1 x as)
remove1-!= {x} {a} as x!=a with (discA x a)
...                         | (yes x==a)  = bot-elim (x!=a x==a)
...                         | (no _)   = refl

remove1-count-pred-refl : (x : A) (as : UList A) -> count x (remove1 x as) == pred (count x as)
remove1-count-pred-refl x = UListElim.prop (isSetNat _ _) []* _::*_
  where
  P : UList A -> Type _
  P as = count x (remove1 x as) == pred (count x as)

  []* : P []
  []* = refl

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  _::*_ a {as} p with (discA x a)
  ...               | (yes x==a)  = refl
  ...               | (no x!=a)   = count-!= (remove1 x as) x!=a >=> p


remove1-count-pred : {x : A} {y : A} (as : UList A) -> (x == y)
                     -> count x (remove1 y as) == pred (count x as)
remove1-count-pred {x} {y} as x==y =
  transport (\ i -> (count x (remove1 (x==y i) as) == (pred (count x as))))
            (remove1-count-pred-refl x as)

remove1-count-ignore : {x : A} {y : A} (as : UList A) -> (x != y)
                       -> count x (remove1 y as) == (count x as)
remove1-count-ignore {x} {y} as x!=y = UListElim.prop (isSetNat _ _) []* _::*_ as
  where
  P : UList A -> Type _
  P as = count x (remove1 y as) == (count x as)

  []* : P []
  []* = refl

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  _::*_ a {as} p with (discA y a)
  ...               | (yes y==a)  = (sym (count-!= as x!=a))
    where
    x!=a : x != a
    x!=a x==a = x!=y (x==a >=> (sym y==a))
  ...               | (no y!=a)   =  proof
    where
    proof : (count x (a :: (remove1 y as))) == (count x (a :: as))
    proof with (discA x a)
    ...      | (yes _) = (cong suc p)
    ...      | (no _)  = p


remove1-count-zero : {x : A} {as : UList A} -> (count x as) == 0 -> (remove1 x as) == as
remove1-count-zero {x} {as} = UListElim.prop PisProp []* _::*_ as
  where
  P : UList A -> Type _
  P as = (count x as) == 0 -> (remove1 x as) == as

  PisProp : {as : UList A} -> isProp (P as)
  PisProp = isPropΠ (\ _ -> (trunc _ _))

  []* : P []
  []* p = refl

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  _::*_ a {as} p with (discA x a)
  ...               | (yes _)     = (\ c -> bot-elim (zero-suc-absurd (sym c)))
  ...               | (no x!=a)   = (\ c i -> a :: p c i)

remove1-count-suc : {x : A} {as : UList A} {n : Nat} -> count x as == (suc n) -> x :: (remove1 x as) == as
remove1-count-suc {x} {as} {n} = UListElim.prop PisProp []* _::*_ as
  where
  P : UList A -> Type _
  P as = (count x as) == (suc n) -> x :: (remove1 x as) == as

  PisProp : {as : UList A} -> isProp (P as)
  PisProp = isPropΠ (\ _ -> (trunc _ _))

  []* : P []
  []* count-p = bot-elim (zero-suc-absurd count-p)

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  _::*_ a {as} f with (discA x a)
  ...               | (yes x==a)  = (\ _ i -> (x==a i) :: as)
  ...               | (no x!=a)   = proof
    where
    proof : (count x as == suc n) -> x :: a :: (remove1 x as) == a :: as
    proof p = (swap x a (remove1 x as)) >=> (\i -> a :: f p i)
