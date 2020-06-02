{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module unordered-list.discrete {ℓ : Level} {A : Type ℓ} (discA : Discrete A) where

open import equality
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

count-== : {x : A} {a : A} (as : UList A) -> (x == a) -> count x (a :: as) == suc (count x as)
count-== {x} {a} as x==a with (discA x a)
...                         | (yes _)     = refl
...                         | (no x!=a)   = bot-elim (x!=a x==a)

count-!= : {x : A} {a : A} (as : UList A) -> (x != a) -> count x (a :: as) == (count x as)
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
