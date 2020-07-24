{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module unordered-list.discrete {ℓ : Level} {A : Type ℓ} {{disc'A : Discrete' A}} where

open import equality
open import hlevel
open import nat
open import unordered-list.base
open import unordered-list.operations

private
  discA = Discrete'.f disc'A

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

count-≤ : (x : A) {a : A} (as : UList A) -> count x as ≤ count x (a :: as)
count-≤ x {a} as = handle (discA x a)
  where
  handle : (Dec (x == a)) -> count x as ≤ count x (a :: as)
  handle (yes x==a) = 1 , sym (count-== as x==a)
  handle (no  x!=a) = 0 , sym (count-!= as x!=a)

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

-- No duplicates

NoDuplicates : UList A -> Type ℓ
NoDuplicates ul = ∀ (a : A) -> count a ul ≤ 1

isPropNoDuplicates : {ul : UList A} -> isProp (NoDuplicates ul)
isPropNoDuplicates = isPropΠ (\_ -> isProp≤)

decide-no-duplicates : (ul : UList A) -> Dec (NoDuplicates ul)
decide-no-duplicates = UListElim.prop {B = P} (\{ul} -> isPropP {ul}) []* ::*
  where
  P : UList A -> Type ℓ
  P ul = Dec (NoDuplicates ul)

  isPropP : {ul : UList A} -> isProp (P ul)
  isPropP {ul} = isPropDec (isPropNoDuplicates {ul})

  []* : Dec (NoDuplicates [])
  []* = yes (\ a -> zero-≤)

  ::* : (a : A) {as : UList A} -> Dec (NoDuplicates as) -> Dec (NoDuplicates (a :: as))
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

-- Count and contains
count-zero->¬contains : {a : A} {as : UList A} -> count a as == 0 -> ¬ (contains a as)
count-zero->¬contains {a} count-p (as' , p) =
  zero-suc-absurd (sym (sym (count-== as' refl) >=> cong (count a) p >=> count-p))

count-suc->contains : {a : A} {as : UList A} {c : Nat} -> count a as == (suc c) -> (contains a as)
count-suc->contains {a} {as} count-p = (remove1 a as) , remove1-count-suc  count-p

contains->count>0 : {a : A} {as : UList A} -> contains a as -> (count a as) > 0
contains->count>0 {a} {as} (as' , path) =
  count a as' ,
  +'-commute {count a as'} {1} >=> (sym (count-== as' refl)) >=> cong (count a) path


decide-contains : (x : A) (as : UList A) -> Dec (contains x as)
decide-contains x as = handle (count x as) refl
  where
  handle : (n : Nat) -> count x as == n -> Dec (contains x as)
  handle zero    p = no (count-zero->¬contains p)
  handle (suc _) p = yes (count-suc->contains p)

-- Filter
module _ {ℓ : Level} {P : A -> Type ℓ} (f : (a : A) -> Dec (P a)) where

  filter-count≤ : (a : A) (as : UList A) -> count a (filter f as) ≤ count a as
  filter-count≤ a as = UListElim.prop isProp≤ zero-≤ ::* as
    where
    ::* : (a2 : A) {as : UList A}
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
