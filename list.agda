{-# OPTIONS --cubical --safe --exact-split #-}

module list where

open import base
open import relation
open import equality
open import monoid
open import nat

private
  variable
    ℓ : Level
    A B : Type ℓ


infixr 5 _::_
data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _::_  : (a : A) -> List A -> List A

infixr 5 _++_
_++_ : List A -> List A -> List A
[] ++ l2 = l2
(a :: l1) ++ l2 = a :: (l1 ++ l2)

[_] : A -> List A
[ a ] = a :: []

map : (A -> B) -> List A -> List B
map f [] = []
map f (e :: l) = f e :: (map f l)

length : (l : List A) -> Nat
length []        = 0
length (_ :: as) = suc (length as)

NonEmpty : List A -> Set
NonEmpty [] = Bot
NonEmpty (_ :: _) = Top

data NonEmptyListBinaryRec (A : Type ℓ) : List A -> Type ℓ where
  elem  : (a : A) -> NonEmptyListBinaryRec A (a :: [])
  _:++:_ : ∀ {as bs} -> NonEmptyListBinaryRec A as -> NonEmptyListBinaryRec A bs
           -> NonEmptyListBinaryRec A (as ++ bs)

non-empty-list-binary-rec : (l : List A) -> {NonEmpty l} -> NonEmptyListBinaryRec A l
non-empty-list-binary-rec (e :: []) = elem e
non-empty-list-binary-rec (e :: l@(_ :: _)) = (elem e) :++: (non-empty-list-binary-rec l)

data ConcatTo {A : Type ℓ} : List A -> List A -> List A -> Set ℓ where
  concat-to-empty : ∀ as -> ConcatTo as [] as
  concat-to-cons : ∀ {as bs cs} a -> ConcatTo as bs cs -> ConcatTo (a :: as) (a :: bs) cs


map-inject-++ : (f : A -> B) {a1 a2 : List A} -> map f (a1 ++ a2) == (map f a1) ++ (map f a2)
map-inject-++ f {[]} = refl
map-inject-++ f {e :: a1} {a2} = cong (\x -> f e :: x) (map-inject-++ f {a1} {a2})


data Insertion (A : Type ℓ) : A -> (List A) -> (List A) -> Type ℓ where
  insertion-base : (a : A) -> (as : (List A)) -> Insertion A a as (a :: as)
  insertion-cons : {a : A} {as1 as2 : (List A)} -> (a2 : A)
                   -> (Insertion A a as1 as2) -> Insertion A a (a2 :: as1) (a2 :: as2)

data Permutation (A : Type ℓ) : (List A) -> (List A) -> Type ℓ where
  permutation-empty : Permutation A [] []
  permutation-cons  : {a : A} -> {as1 as2 as3 : List A}
                      -> Permutation A as1 as2
                      -> Insertion A a as2 as3
                      -> Permutation A (a :: as1) as3


insert : (A -> A -> Boolean) -> A -> List A -> List A
insert _ a [] = a :: []
insert _<_ a (a2 :: as) with a < a2
... | true = a :: (a2 :: as)
... | false = a2 :: (insert _<_ a as)

Insertion-insert : (_<_ : A -> A -> Boolean) -> (a : A) -> (as : (List A))
                   -> Insertion A a as (insert _<_ a as)
Insertion-insert _t a [] = insertion-base a []
Insertion-insert _<_ a (a2 :: as) with a < a2
... | true = insertion-base a (a2 :: as)
... | false = insertion-cons a2 (Insertion-insert _<_ a as)

insertion-sort : (A -> A -> Boolean) -> List A -> List A
insertion-sort _<_ [] = []
insertion-sort _<_ (a :: as) = (insert _<_ a (insertion-sort _<_ as))

Permutation-insertion-sort : (_<_ : A -> A -> Boolean) -> (as : List A)
                             -> Permutation A as (insertion-sort _<_ as)
Permutation-insertion-sort _<_ [] = permutation-empty
Permutation-insertion-sort _<_ (a :: as) =
  (permutation-cons (Permutation-insertion-sort _<_ as)
                    (Insertion-insert _<_ a (insertion-sort _<_ as)))

++-assoc : {a : List A} {b : List A} {c : List A} -> (a ++ b) ++ c == a ++ (b ++ c)
++-assoc {a = []} {b} {c} = refl
++-assoc {a = a :: as} {b} {c} = cong (a ::_) (++-assoc {a = as} {b} {c})

++-left-[] : {a : List A} -> ([] ++ a) == a
++-left-[] = refl

++-right-[] : {a : List A} -> (a ++ []) == a
++-right-[] {a = []} = refl
++-right-[] {a = a :: as} = cong (a ::_) (++-right-[] {a = as})


instance
  ListMonoid : Monoid (List A)
  ListMonoid {A} = record {
    ε = [];
    _∙_ = _++_;
    ∙-assoc = \ {m} {n} {o} -> ++-assoc {a = m} {n} {o};
    ∙-left-ε = ++-left-[];
    ∙-right-ε = ++-right-[]
    }


mapʰ : (f : A -> B) -> Monoidʰ (map f)
mapʰ f = record {
  preserves-ε = refl ;
  preserves-∙ = (\ x y -> map-inject-++ f {x} {y})
  }

concat : {{M : Monoid A}} -> List A -> A
concat {{M = M}} [] = Monoid.ε M
concat {{M = M}} (a :: l) = (Monoid._∙_ M) a (concat l)

concatʰ : {{M : Monoid A}} -> Monoidʰ (concat {{M}})
concatʰ {A = A} {{M = M}} = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  open Monoid M
  preserves-∙ : (x y : List A) -> concat (x ++ y) == (concat x) ∙ (concat y)
  preserves-∙ [] y = sym ∙-left-ε
  preserves-∙ (a :: l) y = cong (a ∙_) (preserves-∙ l y) >=> sym ∙-assoc

lengthʰ : Monoidʰ {D₁ = List A} length
lengthʰ = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  preserves-∙ : (xs ys : List A) -> length (xs ++ ys) == (length xs) +' (length ys)
  preserves-∙ [] ys = refl
  preserves-∙ (_ :: xs) ys = cong suc (preserves-∙ xs ys)

-- Injective
safe-tail : List A -> List A
safe-tail []        = []
safe-tail (_ :: as) = as

safe-head : A -> List A ->  A
safe-head x []        = x
safe-head x (a :: as) = a

::-injective : {a b : A} {as bs : List A} -> a :: as == b :: bs -> as == bs
::-injective p = cong safe-tail p

::-injective' : {a b : A} {as bs : List A} -> a :: as == b :: bs -> a == b
::-injective' {a = a} p = cong (safe-head a) p

++-injective-left : {as bs cs : List A} -> as ++ bs == as ++ cs -> bs == cs
++-injective-left {as = []}        p = p
++-injective-left {as = (a :: as)} p = (++-injective-left (::-injective p))

-- Contains

contains : A -> Pred (List A) _
contains {A = A} a as = Σ[ l ∈ List A ] (Σ[ r ∈ List A ] (l ++ [ a ] ++ r == as))

[]-¬contains : (x : A) -> ¬ (contains x [])
[]-¬contains x ([]     , r , p) = zero-suc-absurd (cong length (sym p))
[]-¬contains x (_ :: _ , r , p) = zero-suc-absurd (cong length (sym p))


list∈ : List A -> Pred A _
list∈ as a = contains a as

ContainsOnly : (Pred A ℓ) -> Pred (List A) _
ContainsOnly P as = (list∈ as) ⊆ P

ContainsAll : (Pred A ℓ) -> Pred (List A) _
ContainsAll P as = P ⊆ (list∈ as)


module _ {ℓ : Level} {P : A -> Type ℓ} (f : (a : A) -> Dec (P a)) where

  private
    split-rec : (a : A) -> List A × List A -> List A × List A
    split-rec a (as1 , as2) = handle (f a)
      where
      handle : Dec (P a) -> List A × List A
      handle (yes _) = a :: as1 , as2
      handle (no  _) = as1 , a :: as2

  split : List A -> (List A × List A)
  split [] = [] , []
  split (a :: as) = split-rec a (split as)

  private
    split-rec-fst-keeps : {a : A} (s : List A × List A) (p : P a)
                      -> fst (split-rec a s) == a :: (fst s)
    split-rec-fst-keeps {a} as p with (f a)
    ... | yes _ = refl
    ... | no ¬p = bot-elim (¬p p)

    split-rec-fst-drops : {a : A} (s : List A × List A) (p : ¬(P a))
                      -> fst (split-rec a s) == (fst s)
    split-rec-fst-drops {a} as ¬p with (f a)
    ... | yes p = bot-elim (¬p p)
    ... | no  _ = refl

    split-rec-snd-keeps : {a : A} (s : List A × List A) (p : ¬(P a))
                      -> snd (split-rec a s) == a :: (snd s)
    split-rec-snd-keeps {a} as ¬p with (f a)
    ... | yes p = bot-elim (¬p p)
    ... | no  _ = refl

    split-rec-snd-drops : {a : A} (s : List A × List A) (p : P a)
                      -> snd (split-rec a s) == (snd s)
    split-rec-snd-drops {a} as p with (f a)
    ... | yes _ = refl
    ... | no ¬p = bot-elim (¬p p)

  split-fst-keeps : {a : A} (as : List A) (p : P a) -> fst (split (a :: as)) == a :: (fst (split as))
  split-fst-keeps as p = split-rec-fst-keeps (split as) p

  split-fst-drops : {a : A} (as : List A) (p : ¬(P a)) -> fst (split (a :: as)) == (fst (split as))
  split-fst-drops as p = split-rec-fst-drops (split as) p

  split-snd-keeps : {a : A} (as : List A) (p : ¬(P a)) -> snd (split (a :: as)) == a :: (snd (split as))
  split-snd-keeps as p = split-rec-snd-keeps (split as) p

  split-snd-drops : {a : A} (as : List A) (p : P a) -> snd (split (a :: as)) == (snd (split as))
  split-snd-drops as p = split-rec-snd-drops (split as) p


  filter : List A -> List A
  filter as = fst (split as)

  filter-keeps : {a : A} (as : List A) (p : P a) -> filter (a :: as) == a :: filter as
  filter-keeps as p = split-fst-keeps as p

  filter-drops : {a : A} (as : List A) (p : ¬(P a)) -> filter (a :: as) == filter as
  filter-drops as p = split-fst-drops as p

--  filter-keeps-single : {a : A} (p : P a) -> filter [ a ] == [ a ]
--  filter-keeps-single = filter-keeps []
--
--  filter-drops-single : {a : A} (p : (¬ (P a)) -> filter [ a ] == [ a ]
--  filter-drops-single = filter-keeps []


  filter' : List A -> List A
  filter' as = snd (split as)

  filter'-keeps : {a : A} (as : List A) (p : ¬(P a)) -> filter' (a :: as) == a :: filter' as
  filter'-keeps as p = split-snd-keeps as p

  filter'-drops : {a : A} (as : List A) (p : P a) -> filter' (a :: as) == filter' as
  filter'-drops as p = split-snd-drops as p

  filter-++ : (as1 as2 : List A) -> filter (as1 ++ as2) == filter as1 ++ filter as2
  filter-++ []         as2 = refl
  filter-++ (a :: as1) as2 = handle (f a)
    where
    handle : (Dec (P a)) -> filter (a :: as1 ++ as2) == filter (a :: as1) ++ filter as2
    handle (yes p) =
      filter-keeps (as1 ++ as2) p
      >=> (\i -> a :: (filter-++ as1 as2 i))
      >=> (\i -> (filter-keeps as1 p (~ i)) ++ (filter as2))
    handle (no ¬p) =
      filter-drops (as1 ++ as2) ¬p
      >=> (filter-++ as1 as2)
      >=> (\i -> (filter-drops as1 ¬p (~ i)) ++ (filter as2))

  filter'-++ : (as1 as2 : List A) -> filter' (as1 ++ as2) == filter' as1 ++ filter' as2
  filter'-++ []         as2 = refl
  filter'-++ (a :: as1) as2 = handle (f a)
    where
    handle : (Dec (P a)) -> filter' (a :: as1 ++ as2) == filter' (a :: as1) ++ filter' as2
    handle (no ¬p) =
      filter'-keeps (as1 ++ as2) ¬p
      >=> (\i -> a :: (filter'-++ as1 as2 i))
      >=> (\i -> (filter'-keeps as1 ¬p (~ i)) ++ (filter' as2))
    handle (yes p) =
      filter'-drops (as1 ++ as2) p
      >=> (filter'-++ as1 as2)
      >=> (\i -> (filter'-drops as1 p (~ i)) ++ (filter' as2))

  filterʰ : Monoidʰ {D₁ = List A} filter
  filterʰ = record
    { preserves-ε = refl
    ; preserves-∙ = filter-++
    }

  filter'ʰ : Monoidʰ {D₁ = List A} filter'
  filter'ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = filter'-++
    }


  split-contains : {a : A} (as : List A) -> contains a as
                   -> (contains a (filter as)) ⊎ (contains a (filter' as))
  split-contains {a} as (l , r , path) = handle (f a)
    where
    handle : (Dec (P a)) -> (contains a (filter as)) ⊎ (contains a (filter' as))
    handle (yes p) = inj-l (filter l , filter r , path')
      where
      path' : filter l ++ [ a ] ++ filter r == (filter as)
      path' =
       (\i -> (filter l ++ (filter-keeps [] p (~ i)) ++ filter r))
       >=> (\i -> (filter l ++ (filter-++ [ a ] r (~ i))))
       >=> (\i -> (filter-++ l ([ a ] ++ r) (~ i)))
       >=> (cong filter path)
    handle (no ¬p) = inj-r (filter' l , filter' r , path')
      where
      path' : filter' l ++ [ a ] ++ filter' r == (filter' as)
      path' =
       (\i -> (filter' l ++ (filter'-keeps [] ¬p (~ i)) ++ filter' r))
       >=> (\i -> (filter' l ++ (filter'-++ [ a ] r (~ i))))
       >=> (\i -> (filter'-++ l ([ a ] ++ r) (~ i)))
       >=> (cong filter' path)

  filter-idempotent : (as : List A) -> filter (filter as) == filter as
  filter-idempotent [] = refl
  filter-idempotent (a :: as) = handle (f a) (filter-idempotent as)
    where
    handle : (Dec (P a))
             -> filter (filter as) == filter as
             -> filter (filter (a :: as)) == filter (a :: as)
    handle (yes p) path =
      cong filter (filter-keeps as p)
      >=> filter-keeps (filter as) p
      >=> cong (a ::_) path
      >=> sym (filter-keeps as p)
    handle (no ¬p) path =
      cong filter (filter-drops as ¬p)
      >=> path
      >=> sym (filter-drops as ¬p)

  filter'-idempotent : (as : List A) -> filter' (filter' as) == filter' as
  filter'-idempotent [] = refl
  filter'-idempotent (a :: as) = handle (f a) (filter'-idempotent as)
    where
    handle : (Dec (P a))
             -> filter' (filter' as) == filter' as
             -> filter' (filter' (a :: as)) == filter' (a :: as)
    handle (no ¬p) path =
      cong filter' (filter'-keeps as ¬p)
      >=> filter'-keeps (filter' as) ¬p
      >=> cong (a ::_) path
      >=> sym (filter'-keeps as ¬p)
    handle (yes p) path =
      cong filter' (filter'-drops as p)
      >=> path
      >=> sym (filter'-drops as p)

  filter-length≤ : (as : List A) -> length (filter as) ≤ length as
  filter-length≤ [] = zero-≤
  filter-length≤ (a :: as) = handle (f a) (filter-length≤ as)
    where
    handle : (Dec (P a))
             -> length (filter as) ≤ length as
             -> length (filter (a :: as)) ≤ length (a :: as)
    handle (yes p) (i , path) = (i , (\k -> i +' length (filter-keeps as p k))
                                     >=> +'-right-suc
                                     >=> cong suc path)
    handle (no ¬p) (i , path) = (suc i , (\k -> suc i +' length (filter-drops as ¬p k))
                                         >=> cong suc path)

  filter'-length≤ : (as : List A) -> length (filter' as) ≤ length as
  filter'-length≤ [] = zero-≤
  filter'-length≤ (a :: as) = handle (f a) (filter'-length≤ as)
    where
    handle : (Dec (P a))
             -> length (filter' as) ≤ length as
             -> length (filter' (a :: as)) ≤ length (a :: as)
    handle (no ¬p) (i , path) = (i , (\k -> i +' length (filter'-keeps as ¬p k))
                                     >=> +'-right-suc
                                     >=> cong suc path)
    handle (yes p) (i , path) = (suc i , (\k -> suc i +' length (filter'-drops as p k))
                                         >=> cong suc path)

  private
    p-count : List A -> Nat
    p-count as = length (filter as)

    p-count-¬P : {a : A} (as : List A) (¬p : ¬(P a)) -> p-count (a :: as) == p-count as
    p-count-¬P as ¬p = cong length (filter-drops as ¬p)

    p-countʰ : Monoidʰ {D₁ = List A} p-count
    p-countʰ = lengthʰ ∘ʰ filterʰ

    p-count-++ : (l r : List A) -> p-count (l ++ r) == p-count l +' p-count r
    p-count-++ = Monoidʰ.preserves-∙ p-countʰ

    filter-contains-only : (as : List A) -> ContainsOnly P (filter as)
    filter-contains-only [] c = bot-elim ([]-¬contains _ c)
    filter-contains-only (a :: as) {a = x} (l1 :: ls , r , p) = handle (f a)
      where
      handle : (Dec (P a)) -> P x
      handle (yes pa) = filter-contains-only as (ls       , r , ::-injective (p >=> filter-keeps as pa))
      handle (no ¬pa) = filter-contains-only as (l1 :: ls , r , (p >=> filter-drops as ¬pa))
    filter-contains-only (a :: as) {a = x} ([] , r , p) = handle (f a)
      where
      handle : (Dec (P a)) -> P x
      handle (yes pa) = transport (\i -> P (x==a (~ i))) pa
        where
        x==a : x == a
        x==a = ::-injective' (p >=> filter-keeps as pa)
      handle (no ¬pa) = filter-contains-only as ([] , r , (p >=> filter-drops as ¬pa))

    filter'-contains-only : (as : List A) -> ContainsOnly (Comp P) (filter' as)
    filter'-contains-only [] c = bot-elim ([]-¬contains _ c)
    filter'-contains-only (a :: as) {a = x} (l1 :: ls , r , p) = handle (f a)
      where
      handle : (Dec (P a)) -> ¬ (P x)
      handle (yes pa) =
        filter'-contains-only as (l1 :: ls , r , (p >=> filter'-drops as pa))
      handle (no ¬pa) =
        filter'-contains-only as (ls       , r , ::-injective (p >=> filter'-keeps as ¬pa))
    filter'-contains-only (a :: as) {a = x} ([] , r , p) = handle (f a)
      where
      handle : (Dec (P a)) -> ¬ (P x)
      handle (no ¬pa) = transport (\i -> ¬ (P (x==a (~ i)))) ¬pa
        where
        x==a : x == a
        x==a = ::-injective' (p >=> filter'-keeps as ¬pa)
      handle (yes pa) = filter'-contains-only as ([] , r , (p >=> filter'-drops as pa))

  filter-contains-all : {as : List A}
                        -> ContainsAll P as
                        -> ContainsAll P (filter as)
  filter-contains-all {as = as} g {a = x} px = handle (split-contains as (g px))
    where
    handle : (contains x (filter as)) ⊎ (contains x (filter' as)) -> contains x (filter as)
    handle (inj-l in-f ) = in-f
    handle (inj-r in-f') = bot-elim (filter'-contains-only as in-f' px)
