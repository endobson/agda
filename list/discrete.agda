{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module list.discrete {ℓ : Level} {A : Type ℓ} {{disc'A : Discrete' A}} where

open import equality
open import hlevel
open import list
open import nat

private
  discA = Discrete'.f disc'A

count : (x : A) -> List A -> Nat
count x [] = 0
count x (a :: as) = handle (discA x a) (count x as)
  where
  handle : {a : A} -> (Dec (x == a)) -> Nat -> Nat
  handle (yes _) n = suc n
  handle (no _)  n = n

count-== : {x : A} {a : A} (as : List A) -> x == a -> count x (a :: as) == suc (count x as)
count-== {x} {a} as x==a with (discA x a)
...                         | (yes _)     = refl
...                         | (no x!=a)   = bot-elim (x!=a x==a)

count-!= : {x : A} {a : A} (as : List A) -> x != a -> count x (a :: as) == (count x as)
count-!= {x} {a} as x!=a with (discA x a)
...                         | (yes x==a)  = bot-elim (x!=a x==a)
...                         | (no _)   = refl

count-≤ : (x : A) {a : A} (as : List A) -> count x as ≤ count x (a :: as)
count-≤ x {a} as = handle (discA x a)
  where
  handle : (Dec (x == a)) -> count x as ≤ count x (a :: as)
  handle (yes x==a) = 1 , sym (count-== as x==a)
  handle (no  x!=a) = 0 , sym (count-!= as x!=a)

remove1 : (x : A) -> List A -> List A
remove1 x [] = []
remove1 x (a :: as) with (discA x a)
...                    | (yes _)     = as
...                    | (no  _)     = a :: (remove1 x as)


remove1-== : {x : A} {a : A} (as : List A) -> (x == a) -> remove1 x (a :: as) == as
remove1-== {x} {a} as x==a with (discA x a)
...                         | (yes _)     = refl
...                         | (no x!=a)   = bot-elim (x!=a x==a)

remove1-!= : {x : A} {a : A} (as : List A) -> (x != a) -> remove1 x (a :: as) == a :: (remove1 x as)
remove1-!= {x} {a} as x!=a with (discA x a)
...                         | (yes x==a)  = bot-elim (x!=a x==a)
...                         | (no _)   = refl

remove1-count-pred-refl : (x : A) (as : List A) -> count x (remove1 x as) == pred (count x as)
remove1-count-pred-refl x [] = refl
remove1-count-pred-refl x (a :: as) = handle (discA x a) (remove1-count-pred-refl x as)
  where
  P : List A -> Type _
  P as = count x (remove1 x as) == pred (count x as)

  handle : (Dec (x == a)) -> P as -> P (a :: as)
  handle (yes x==a) p =
    cong (count x) (remove1-== as x==a)
    >=> cong pred (sym (count-== as x==a))
  handle (no  x!=a) p =
    cong (count x) (remove1-!= as x!=a)
    >=> (count-!= (remove1 x as) x!=a)
    >=> p
    >=> sym (cong pred (count-!= as x!=a))


remove1-count-pred : {x : A} {y : A} (as : List A) -> (x == y)
                     -> count x (remove1 y as) == pred (count x as)
remove1-count-pred {x} {y} as x==y =
  transport (\ i -> (count x (remove1 (x==y i) as) == (pred (count x as))))
            (remove1-count-pred-refl x as)

remove1-count-ignore : {x : A} {y : A} (as : List A) -> (x != y)
                       -> count x (remove1 y as) == (count x as)
remove1-count-ignore {x} {y} []        x!=y = refl
remove1-count-ignore {x} {y} (a :: as) x!=y = handle a (remove1-count-ignore as x!=y)
  where
  P : List A -> Type _
  P as = count x (remove1 y as) == (count x as)

  handle : (a : A) -> {as : List A} -> P as -> P (a :: as)
  handle a {as} p with (discA y a)
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


remove1-count-zero : {x : A} {as : List A} -> (count x as) == 0 -> (remove1 x as) == as
remove1-count-zero {x} {[]} p = refl
remove1-count-zero {x} {a :: as} = a ::* (remove1-count-zero {as = as})
  where
  P : List A -> Type _
  P as = (count x as) == 0 -> (remove1 x as) == as

  _::*_ : (a : A) -> {as : List A} -> P as -> P (a :: as)
  _::*_ a {as} p with (discA x a)
  ...               | (yes _)     = (\ c -> bot-elim (zero-suc-absurd (sym c)))
  ...               | (no x!=a)   = (\ c i -> a :: p c i)


-- No duplicates

NoDuplicates : List A -> Type ℓ
NoDuplicates l = ∀ (a : A) -> count a l ≤ 1

isPropNoDuplicates : {l : List A} -> isProp (NoDuplicates l)
isPropNoDuplicates = isPropΠ (\_ -> isProp≤)

decide-no-duplicates : (l : List A) -> Dec (NoDuplicates l)
decide-no-duplicates []        = yes (\ a -> zero-≤)
decide-no-duplicates (a :: as) = ::* a {as} (decide-no-duplicates as)
  where
  ::* : (a : A) {as : List A} -> Dec (NoDuplicates as) -> Dec (NoDuplicates (a :: as))
  ::* a {as} (yes f) with (f a)
  ... | (0 , p) = no ¬f
    where
    ¬f : ¬ ((a2 : A) -> count a2 (a :: as) ≤ 1)
    ¬f f' = zero-≮ (pred-≤ (transport (\i -> count-path i ≤ 1) (f' a)))
      where
      count-path : count a (a :: as) == 2
      count-path = count-== as refl >=> cong suc p
  ... | (1 , p) = yes g
    where
    g : ((a2 : A) -> count a2 (a :: as) ≤ 1)
    g a2 = handle (discA a2 a)
      where
      handle : Dec (a2 == a) -> count a2 (a :: as) ≤ 1
      handle (yes a-path) = (0 , count-path >=> count-path2)
        where
        count-path : count a2 (a :: as) == suc (count a2 as)
        count-path = count-== as a-path
        count-path2 : (suc (count a2 as)) == 1
        count-path2 = transport (\i -> suc (count (a-path (~ i)) as) == 1) p
      handle (no ¬a-path) = (transport (\i -> (count-path (~ i)) ≤ 1) (f a2))
        where
        count-path : count a2 (a :: as) == count a2 as
        count-path = count-!= as ¬a-path
  ... | (suc (suc x) , p) = bot-elim (zero-suc-absurd (\i -> (pred (p (~ i)))))
  ::* a {as} (no ¬f) = (no ¬g)
    where
    ¬g : ¬ ((a2 : A) -> count a2 (a :: as) ≤ 1)
    ¬g g = ¬f f
      where
      f : (a2 : A) -> count a2 as ≤ 1
      f a2 with (discA a2 a)
      ... | yes a-path = right-suc-≤ (pred-≤ (transport (\i -> count-path i ≤ 1) (g a2)))
        where
        count-path : count a2 (a :: as) == suc (count a2 as)
        count-path = count-== as a-path
      ... | no ¬a-path = transport (\i -> count-path i ≤ 1) (g a2)
        where
        count-path : count a2 (a :: as) == count a2 as
        count-path = count-!= as ¬a-path

-- NoDuplicates and contains
ContainsExactlyOnce : ∀ {ℓ} -> Pred A ℓ -> Pred (List A) _
ContainsExactlyOnce P = ContainsExactly P ∩ NoDuplicates


--
---- Count and contains
--count-zero->¬contains : {a : A} {as : UList A} -> count a as == 0 -> ¬ (contains a as)
--count-zero->¬contains {a} count-p (as' , p) =
--  zero-suc-absurd (sym (sym (count-== as' refl) >=> cong (count a) p >=> count-p))
--
--count-suc->contains : {a : A} {as : UList A} {c : Nat} -> count a as == (suc c) -> (contains a as)
--count-suc->contains {a} {as} count-p = (remove1 a as) , remove1-count-suc  count-p
--
--decide-contains : (x : A) (as : UList A) -> Dec (contains x as)
--decide-contains x as = handle (count x as) refl
--  where
--  handle : (n : Nat) -> count x as == n -> Dec (contains x as)
--  handle zero    p = no (count-zero->¬contains p)
--  handle (suc _) p = yes (count-suc->contains p)

-- Filter
module _ {ℓ : Level} {P : A -> Type ℓ} (f : (a : A) -> Dec (P a)) where

  filter-count≤ : (a : A) (as : List A) -> count a (filter f as) ≤ count a as
  filter-count≤ a [] = zero-≤
  filter-count≤ a (a2 :: as) = ::* a2 {as} (filter-count≤ a as)
    where
    ::* : (a2 : A) {as : List A}
          -> count a (filter f as) ≤ count a as
          -> count a (filter f (a2 :: as)) ≤ count a (a2 :: as)
    ::* a2 {as} lt = handle (f a2) (discA a a2)
      where
      handle : Dec (P a2) -> Dec (a == a2)
               -> count a (filter f (a2 :: as)) ≤ count a (a2 :: as)
      handle (yes pa2) (yes a==a2) = transport (\i -> (l-path (~ i)) ≤ (r-path (~ i))) (suc-≤ lt)
        where
        l-path : count a (filter f (a2 :: as)) == suc (count a (filter f as))
        l-path = cong (count a) (filter-keeps f as pa2)
                 >=> count-== (filter f as) a==a2

        r-path : count a (a2 :: as) == suc (count a as)
        r-path = count-== as a==a2

      handle (yes pa2) (no a!=a2)  = transport (\i -> (l-path (~ i)) ≤ (r-path (~ i))) lt
        where
        l-path : count a (filter f (a2 :: as)) == count a (filter f as)
        l-path = cong (count a) (filter-keeps f as pa2)
                 >=> count-!= (filter f as) a!=a2

        r-path : count a (a2 :: as) == (count a as)
        r-path = count-!= as a!=a2

      handle (no ¬pa2) _  =
        transport (\i -> count a ((filter-drops f as ¬pa2) (~ i)) ≤ count a (a2 :: as))
                  (trans-≤ lt (count-≤ a as))

  filter-no-duplicates : {as : List A} -> NoDuplicates as -> NoDuplicates (filter f as)
  filter-no-duplicates {as} no-dupes a = trans-≤ (filter-count≤ a as) (no-dupes a)
