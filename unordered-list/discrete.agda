{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module unordered-list.discrete {ℓ : Level} {A : Type ℓ} {{disc'A : Discrete' A}} where

open import additive-group.instances.nat
open import commutative-monoid
open import equality-path
open import functions
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import semiring.instances.nat
open import sigma.base
open import unordered-list.base
open import unordered-list.operations


open import ring.lists NatSemiring

private
  discA = Discrete'.f disc'A

  isPropDecA : {a b : A} -> isProp (Dec (a == b))
  isPropDecA {a} {b} = isPropDec (Discrete->isSet discA a b)

  indicator' : {a b : A} -> Dec (a == b) -> Nat
  indicator' (yes _) = 1
  indicator' (no _) = 0

  indicator : A -> A -> Nat
  indicator x a = indicator' (discA x a)

  indicator-1 : {a b : A} -> a == b -> indicator a b == 1
  indicator-1 {a} {b} a=b = handle (discA a b) refl
    where
    handle : (dec : Dec (a == b)) -> discA a b == dec -> indicator a b == 1
    handle (yes _) p i = indicator' (p i)
    handle (no a!=b) p = bot-elim (a!=b a=b)

  indicator-0 : {a b : A} -> a != b -> indicator a b == 0
  indicator-0 {a} {b} a!=b = handle (discA a b) refl
    where
    handle : (dec : Dec (a == b)) -> discA a b == dec -> indicator a b == 0
    handle (yes a=b) p = bot-elim (a!=b a=b)
    handle (no _) p i = indicator' (p i)

count : (x : A) -> UList A -> Nat
count x = unordered-sum ∘ (map (indicator x))

count-== : {x : A} {a : A} (as : UList A) -> x == a -> count x (a :: as) == suc (count x as)
count-== {x} {a} as x=a i = (indicator-1 x=a i) +' (count x as)

count-!= : {x : A} {a : A} (as : UList A) -> x != a -> count x (a :: as) == (count x as)
count-!= {x} {a} as x!=a i = (indicator-0 x!=a i) +' (count x as)

count-≤ : (x : A) {a : A} (as : UList A) -> count x as ≤ count x (a :: as)
count-≤ x {a} as = handle (discA x a)
  where
  handle : (Dec (x == a)) -> count x as ≤ count x (a :: as)
  handle (yes x==a) = 1 , sym (count-== as x==a)
  handle (no  x!=a) = 0 , sym (count-!= as x!=a)


private
  module _ (x : A) where
    Pair : Type ℓ
    Pair = (Σ[ a ∈ A ] (Dec (x == a)))

    pair : UList A -> UList Pair
    pair = map (\a -> a , discA x a)

    unpair : UList Pair -> UList A
    unpair = map fst

    unpair-pair : (as : UList A) -> unpair (pair as) == as
    unpair-pair as = double-map _ _ as >=> map-id as

    remove-match : UList Pair -> UList Pair
    remove-match [] = []
    remove-match (  (_ , (yes _)) :: ps) = ps
    remove-match (p@(_ , (no _))  :: ps) = p :: (remove-match ps)
    remove-match (trunc as1 as2 p q i j) =
      (trunc (remove-match as1) (remove-match as2)
             (\i -> (remove-match (p i)))
             (\i -> (remove-match (q i))) i j)
    remove-match (swap p1@(_ , (no _)) p2@(_ , (no _)) ps i) =
      swap p1 p2 (remove-match ps) i
    remove-match (swap p1@(_ , (no _)) (_ , (yes _)) ps i) =
      p1 :: ps
    remove-match (swap (_ , (yes _)) p2@(_ , (no _)) ps i) =
      p2 :: ps
    remove-match (swap p1@(a1 , (yes q1)) p2@(a2 , (yes q2)) ps i) =
      path i :: ps
      where
      path : p2 == p1
      path = (ΣProp-path isPropDecA (sym q2 >=> q1))

    pair-dec : {a : A} (as : UList A) (d : Dec (x == a)) -> pair (a :: as) == (a , d) :: pair as
    pair-dec {a} as d i = (a , (isPropDecA (discA x a) d i)) :: pair as

remove1 : (x : A) -> UList A -> UList A
remove1 x = unpair x ∘ remove-match x ∘ pair x

remove1-== : {x a : A} -> (as : UList A) -> x == a -> remove1 x (a :: as) == as
remove1-== {x} as x=a =
  cong (unpair x ∘ remove-match x) (pair-dec x as (yes x=a)) >=>
  unpair-pair x as

remove1-!= : {x a : A} -> (as : UList A) -> x != a -> remove1 x (a :: as) == a :: remove1 x as
remove1-!= {x} as x!=a =
  cong (unpair x ∘ remove-match x) (pair-dec x as (no x!=a))

remove1-count-pred-refl : (x : A) (as : UList A) -> count x (remove1 x as) == pred (count x as)
remove1-count-pred-refl x = UListElim.prop (isSetNat _ _) []* _::*_
  where
  P : UList A -> Type ℓ-zero
  P as = count x (remove1 x as) == pred (count x as)

  []* : P []
  []* = refl

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  _::*_ a {as} p = handle (discA x a)
    where
    handle : Dec (x == a) -> P (a :: as)
    handle (yes x=a) =
      cong (count x) (remove1-== as x=a) >=>
      cong pred (sym (count-== as x=a))
    handle (no x!=a) =
      cong (count x) (remove1-!= as x!=a) >=>
      count-!= (remove1 x as) x!=a >=>
      p >=>
      cong pred (sym (count-!= as x!=a))


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
  _::*_ a {as} p = handle (discA y a) (discA x a)
    where
    handle : Dec (y == a) -> Dec (x == a) -> P (a :: as)
    handle (yes y=a) _ =
      cong (count x) (remove1-== as y=a) >=>
      sym (count-!= as x!=a)
      where
      x!=a : x != a
      x!=a x=a = x!=y (x=a >=> (sym y=a))
    handle (no y!=a) (yes x=a) =
      cong (count x) (remove1-!= as y!=a) >=>
      count-== (remove1 y as) x=a >=>
      cong suc p >=>
      sym (count-== as x=a)
    handle (no y!=a) (no x!=a) =
      cong (count x) (remove1-!= as y!=a) >=>
      count-!= (remove1 y as) x!=a >=>
      p >=>
      sym (count-!= as x!=a)


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
  _::*_ a {as} f = handle (discA x a)
    where
    handle : (Dec (x == a)) -> P (a :: as)
    handle (yes x=a) c=sn i =
      x=a i :: remove1-== as x=a i
    handle (no x!=a) c=sn =
      cong (x ::_) (remove1-!= as x!=a) >=>
      swap x a (remove1 x as) >=>
      cong (a ::_) (f (sym (count-!= as x!=a) >=> c=sn))

-- No duplicates

NoDuplicates : UList A -> Type ℓ
NoDuplicates ul = ∀ (a : A) -> count a ul ≤ 1

isPropNoDuplicates : {ul : UList A} -> isProp (NoDuplicates ul)
isPropNoDuplicates = isPropΠ (\_ -> isProp-≤)

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

¬contains->count==0 : {a : A} (as : UList A) -> ¬(contains a as) -> count a as == 0
¬contains->count==0 {a = x} as = UListElim.prop PisProp []* ::* as
  where
  P : UList A -> Type _
  P as = ¬(contains x as) -> count x as == 0

  PisProp : {as : UList A} -> isProp (P as)
  PisProp {as} = isPropΠ (\_ -> (isSetNat _ _))

  []* : P []
  []* _ = refl

  ::* : (a : A) {as : UList A} -> P as -> P (a :: as)
  ::* a {as} f g = count-!= as x!=a >=> f ¬c-x
    where
    x!=a : x != a
    x!=a x==a = g (as , (\i -> x==a i :: as))

    ¬c-x : ¬ (contains x as)
    ¬c-x (as' , path) = g ((a :: as') , (swap x a as' >=> cong (a ::_) path))


decide-contains : (x : A) (as : UList A) -> Dec (contains x as)
decide-contains x as = handle (count x as) refl
  where
  handle : (n : Nat) -> count x as == n -> Dec (contains x as)
  handle zero    p = no (count-zero->¬contains p)
  handle (suc _) p = yes (count-suc->contains p)

-- Filter
module _ {ℓ : Level} {P : A -> Type ℓ} (f : (a : A) -> Dec (P a)) where

  filter-count≤ : (a : A) (as : UList A) -> count a (filter f as) ≤ count a as
  filter-count≤ a as = UListElim.prop isProp-≤ zero-≤ ::* as
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

-- Monoid homomorphism for count

countʰ : (x : A) -> CommMonoidʰᵉ _ _ (count x)
countʰ x = CommMonoidʰ-∘ unordered-sumʰ mapʰ


-- If A is Discrete then (contains a as) is a proposition

isPropContainsDiscrete : {x : A} {as : UList A} -> isProp (contains x as)
isPropContainsDiscrete {x} {as} (as1 , p1) (as2 , p2) =
  ΣProp-path (trunc _ _) path
  where
  path' : x :: as1 == x :: as2
  path' = p1 >=> sym p2

  path : as1 == as2
  path = sym (remove1-== as1 refl) >=> cong (remove1 x) path' >=> (remove1-== as2 refl)

stable-contains : {x : A} {as : UList A} -> Stable (contains x as)
stable-contains {x} {as} = Dec->Stable (decide-contains x as)

contains-:: : (a : A) {x : A} {as : UList A} -> (contains x as) -> (contains x (a :: as))
contains-:: a {x} {as} (as' , path) = (a :: as' , (swap x a as') >=> cong (a ::_) path)


private
  ¬contains-++' : (x : A) (as1 as2 : UList A)
                 -> ¬(contains x as1)
                 -> (contains x (as1 ++ as2))
                 -> (contains x as2)
  ¬contains-++' x as1 as2 = UListElim.prop PisProp []* ::* as1
    where
    P : UList A -> Type _
    P as = ¬ (contains x as) -> (contains x (as ++ as2)) -> (contains x as2)

    PisProp : {as : UList A} -> isProp (P as)
    PisProp = isPropΠ2 (\_ _ -> isPropContainsDiscrete)

    []* : P []
    []* _ c = c

    ::* : (a : A) -> {as : UList A} -> P as -> P (a :: as)
    ::* a {as} f ¬c-a-as (as' , path) = handle (discA x a)
      where
      ¬c-as : ¬ (contains x as)
      ¬c-as c-as = ¬c-a-as (contains-:: a c-as)

      check-f : (contains x (as ++ as2)) -> (contains x as2)
      check-f = f ¬c-as

      check-path : x :: as' == a :: as ++ as2
      check-path = path

      handle : Dec (x == a) -> (contains x as2)
      handle (yes p) = bot-elim (¬c-a-as (as , (cong (_:: as) p)))
      handle (no ¬p) = check-f (remove1 a as' , path')
        where
        path' : x :: (remove1 a as') == as ++ as2
        path' =
          begin
            x :: (remove1 a as')
          ==< sym (remove1-!= as' (¬p ∘ sym)) >
            remove1 a (x :: as')
          ==< cong (remove1 a) path >
            remove1 a (a :: as ++ as2)
          ==< remove1-== (as ++ as2) refl >
            as ++ as2
          end

¬contains-++ : (x : A) (as1 as2 : UList A)
               -> ¬(contains x as1)
               -> ¬(contains x as2)
               -> ¬(contains x (as1 ++ as2))
¬contains-++ x as1 as2 ¬c1 ¬c2 c12 = ¬c2 (¬contains-++' x as1 as2 ¬c1 c12)

split-contains-++ : (x : A) (as1 as2 : UList A)
                    -> contains x (as1 ++ as2)
                    -> (contains x as1) ⊎ (contains x as2)
split-contains-++ x as1 as2 c-as1-as2 = handle (decide-contains x as1) (decide-contains x as2)
  where
  handle : Dec (contains x as1) -> Dec (contains x as2) -> (contains x as1) ⊎ (contains x as2)
  handle (yes c-as1) _           = (inj-l c-as1)
  handle (no ¬c-as1) (yes c-as2) = (inj-r c-as2)
  handle (no ¬c-as1) (no ¬c-as2) = bot-elim (¬contains-++ x as1 as2 ¬c-as1 ¬c-as2 c-as1-as2)
