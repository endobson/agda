{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module list.discrete {ℓ : Level} {A : Type ℓ} {{disc'A : Discrete' A}} where

open import equality
open import hlevel
open import list
open import list.filter
open import nat

private
  discA = Discrete'.f disc'A

isSetA : isSet A
isSetA = Discrete->isSet discA

private
  indicator : {x a : A} -> (Dec (x == a)) -> Nat
  indicator (yes _) = 1
  indicator (no _) = 0

  indicator==1 : {x a : A} -> x == a -> indicator (discA x a) == 1
  indicator==1 {x} {a} p = cong indicator (isPropDec (isSetA x a) (discA x a) (yes p))

  indicator==0 : {x a : A} -> x != a -> indicator (discA x a) == 0
  indicator==0 {x} {a} p = cong indicator (isPropDec (isSetA x a) (discA x a) (no p))

count : (x : A) -> List A -> Nat
count x [] = 0
count x (a :: as) = (indicator (discA x a)) +' (count x as)

count-== : {x : A} {a : A} (as : List A) -> x == a -> count x (a :: as) == suc (count x as)
count-== as x==a = +'-left (indicator==1 x==a)

count-!= : {x : A} {a : A} (as : List A) -> x != a -> count x (a :: as) == (count x as)
count-!= as x!=a = +'-left (indicator==0 x!=a)

count-≤ : (x : A) {a : A} (as : List A) -> count x as ≤ count x (a :: as)
count-≤ x {a} as = handle (discA x a)
  where
  handle : (Dec (x == a)) -> count x as ≤ count x (a :: as)
  handle (yes x==a) = 1 , sym (count-== as x==a)
  handle (no  x!=a) = 0 , sym (count-!= as x!=a)

count-++ : (a : A) (as bs : List A) -> count a (as ++ bs) == count a as +' count a bs
count-++ a []         bs = refl
count-++ a (a2 :: as) bs = handle (discA a a2)
  where
  handle : (Dec (a == a2)) -> count a (a2 :: as ++ bs) == count a (a2 :: as) +' count a bs
  handle (yes p) =
    count-== (as ++ bs) p
    >=> cong suc (count-++ a as bs)
    >=> +'-left (sym (count-== as p))
  handle (no p) =
    count-!= (as ++ bs) p
    >=> (count-++ a as bs)
    >=> +'-left (sym (count-!= as p))


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

remove1-count≤ : {x : A} {y : A} (as : List A)
                  -> count x (remove1 y as) ≤ (count x as)
remove1-count≤ {x} {y} as = handle (discA x y)
  where
  handle : Dec (x == y) -> count x (remove1 y as) ≤ (count x as)
  handle (yes p) = pred-==-≤ (remove1-count-pred as p)
  handle (no p) = (0 , remove1-count-ignore as p)


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


---- Count and contains


contains->count>0 : {a : A} (as : List A) -> contains a as -> (count a as) > 0
contains->count>0 {a} (a2 :: as) (0 , p) = (count a as , path)
  where
  path : (count a as) +' 1 == count a (a2 :: as)
  path = +'-commute {count a as} {1} >=> sym (count-== as p)
contains->count>0 {a} (a2 :: as) (suc n , p) = trans-≤ count-as (count-≤ a as)
  where
  count-as : (count a as) > 0
  count-as = contains->count>0 as (n , p)

count-zero->¬contains : {a : A} (as : List A) -> count a as == 0 -> ¬ (contains a as)
count-zero->¬contains as count-a contain-a =
  zero-≮ (transport (\i -> 0 < count-a i) (contains->count>0 as contain-a))

count-suc->contains : {a : A} (as : List A) {c : Nat} -> count a as == (suc c) -> (contains a as)
count-suc->contains {a} []         count-a = bot-elim (zero-suc-absurd count-a)
count-suc->contains {a} (a2 :: as) count-a = handle (discA a a2)
  where
  handle : Dec (a == a2) -> contains a (a2 :: as)
  handle (yes p) = (0 , p)
  handle (no  p) = cons-contains a2 (count-suc->contains as (sym (count-!= as p) >=> count-a))

decide-contains : (x : A) (as : List A) -> Dec (contains x as)
decide-contains x as = handle (count x as) refl
  where
  handle : (n : Nat) -> count x as == n -> Dec (contains x as)
  handle zero    p = no (count-zero->¬contains as p)
  handle (suc _) p = yes (count-suc->contains as p)

-- No duplicates

decide-no-duplicates : (l : List A) -> Dec (NoDuplicates l)
decide-no-duplicates []        = yes (lift tt)
decide-no-duplicates (a :: as) = ::* (decide-contains a as) (decide-no-duplicates as)
  where
  ::* : Dec (contains a as) -> Dec (NoDuplicates as) -> Dec (NoDuplicates (a :: as))
  ::* (yes c) (yes nd) = no (\ (¬c , nd) -> bot-elim (¬c c))
  ::* (yes c) (no ¬nd) = no (\ (¬c , nd) -> bot-elim (¬c c))
  ::* (no ¬c) (yes nd) = yes (¬c , nd)
  ::* (no ¬c) (no ¬nd) = no (\ (¬c , nd) -> bot-elim (¬nd nd))

-- Subset with discrete properties

contains-remove1 : {x a : A} {as : List A} -> contains x as -> x != a -> contains x (remove1 a as)
contains-remove1 {x} {a} {as} c p =
  count-suc->contains (remove1 a as)
    (sym (sym +'-right-suc
          >=> (snd (contains->count>0 as c))
          >=> (sym (remove1-count-ignore as p))))

remove1-permutation : {a : A} {as : List A} -> contains a as -> Permutation A as (a :: (remove1 a as))
remove1-permutation {a} {as = b :: as} c = handle (discA a b)
  where
  handle : Dec (a == b) -> Permutation A (b :: as) (a :: (remove1 a (b :: as)))
  handle (yes a==b) =
    transport (\i -> Permutation A (b :: as) ((a==b (~ i)) :: (remove1-== as a==b (~ i))))
              (permutation-same (b :: as))
  handle (no a!=b) =
    transport (\i -> Permutation A (b :: as) (a :: path i)) rec-perm'
    where
    rec-perm : Permutation A as (a :: (remove1 a as))
    rec-perm = remove1-permutation (contains-!= a!=b c)

    rec-perm' : Permutation A (b :: as) (a :: b :: remove1 a as)
    rec-perm' = permutation-compose (permutation-cons b rec-perm)
                                    (permutation-swap b a (remove1 a as))

    path : b :: (remove1 a as) == (remove1 a (b :: as))
    path = sym (remove1-!= as a!=b)



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

-- Decidable properties of the list

discreteList : Discrete (List A)
discreteList []        []        = yes refl
discreteList (a :: as) []        = no (\ p -> zero-suc-absurd (cong length (sym p)))
discreteList []        (b :: bs) = no (\ p -> zero-suc-absurd (cong length p))
discreteList (a :: as) (b :: bs) = handle (discA a b) (discreteList as bs)
  where
  handle : (Dec (a == b)) -> (Dec (as == bs)) -> Dec ((a :: as) == (b :: bs))
  handle (yes p1) (yes p2) = yes (\i -> (p1 i) :: (p2 i))
  handle (yes p1) (no f)   = no (\p -> f (::-injective p))
  handle (no f)   _        = no (\p -> f (::-injective' p))
