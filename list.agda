{-# OPTIONS --cubical --safe --exact-split #-}

module list where

open import base
open import relation
open import equality
open import functions
open import monoid
open import nat
open import sum

private
  variable
    ℓ : Level
    A B C : Type ℓ


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

double-map : (f : B -> C) (g : A -> B) (as : List A)
             -> map f (map g as) == map (f ∘ g) as
double-map {A = A} f g [] = refl
double-map {A = A} f g (a :: as) = cong ((f (g a)) ::_) (double-map f g as)


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


data Permutation (A : Type ℓ) : (List A) -> (List A) -> Type ℓ where
  permutation-empty : Permutation A [] []
  permutation-cons : (a : A) -> {as1 as2 : List A} -> Permutation A as1 as2
                     -> Permutation A (a :: as1) (a :: as2)
  permutation-swap : (a1 a2 : A) -> (as : List A)
                     -> Permutation A (a1 :: a2 :: as) (a2 :: a1 :: as)
  permutation-compose : {as1 as2 as3 : List A}
                        -> Permutation A as1 as2 -> Permutation A as2 as3
                        -> Permutation A as1 as3

permutation-same : (as : List A) -> Permutation A as as
permutation-same []        = permutation-empty
permutation-same (a :: as) = permutation-cons a (permutation-same as)

permutation-== : {as bs : List A} -> as == bs -> Permutation A as bs
permutation-== {A = A} {as = as} p = transport (\i -> Permutation A as (p i)) (permutation-same as)

insert : (A -> A -> Boolean) -> A -> List A -> List A
insert _ a [] = a :: []
insert _<_ a (a2 :: as) with a < a2
... | true = a :: (a2 :: as)
... | false = a2 :: (insert _<_ a as)


Permutation-insert : (_<_ : A -> A -> Boolean) -> (a : A) -> (as : (List A))
                      -> Permutation A (a :: as) (insert _<_ a as)
Permutation-insert _t a [] = permutation-same [ a ]
Permutation-insert _<_ a (a2 :: as) with a < a2
... | true = permutation-same (a :: a2 :: as)
... | false =
  permutation-compose
    (permutation-swap a a2 _)
    (permutation-cons a2 (Permutation-insert _<_ a as))

insertion-sort : (A -> A -> Boolean) -> List A -> List A
insertion-sort _<_ [] = []
insertion-sort _<_ (a :: as) = (insert _<_ a (insertion-sort _<_ as))

Permutation-insertion-sort : (_<_ : A -> A -> Boolean) -> (as : List A)
                             -> Permutation A as (insertion-sort _<_ as)
Permutation-insertion-sort _<_ [] = permutation-empty
Permutation-insertion-sort _<_ (a :: as) =
  (permutation-compose
    (permutation-cons a (Permutation-insertion-sort _<_ as))
    (Permutation-insert _<_ a _))

permutation-flip : {as bs : List A} -> Permutation A as bs -> Permutation A bs as
permutation-flip permutation-empty = permutation-empty
permutation-flip (permutation-cons a p) =
  permutation-cons a (permutation-flip p)
permutation-flip (permutation-swap a b p) = permutation-swap b a p
permutation-flip (permutation-compose p1 p2) =
  permutation-compose (permutation-flip p2) (permutation-flip p1)

permutation-length== : {as bs : List A} -> Permutation A as bs -> length as == length bs
permutation-length== (permutation-empty) = refl
permutation-length== (permutation-cons _ p) = cong suc (permutation-length== p)
permutation-length== (permutation-swap a b l) = refl
permutation-length== (permutation-compose p1 p2) = permutation-length== p1 >=> permutation-length== p2

++-assoc : {a : List A} {b : List A} {c : List A} -> (a ++ b) ++ c == a ++ (b ++ c)
++-assoc {a = []} {b} {c} = refl
++-assoc {a = a :: as} {b} {c} = cong (a ::_) (++-assoc {a = as} {b} {c})

++-left-[] : {as : List A} -> ([] ++ as) == as
++-left-[] = refl

++-right-[] : {as : List A} -> (as ++ []) == as
++-right-[] {as = []} = refl
++-right-[] {as = a :: as} = cong (a ::_) (++-right-[] {as = as})


permutation-snoc : (a : A) (bs : List A) -> Permutation A ([ a ] ++ bs) (bs ++ [ a ])
permutation-snoc a []        = permutation-same [ a ]
permutation-snoc a (b :: bs) =
  permutation-compose (permutation-swap a b bs) (permutation-cons b (permutation-snoc a bs))

permutation-++-left : {as bs : List A} -> Permutation A as bs -> (cs : List A)
                      -> Permutation A (as ++ cs) (bs ++ cs)
permutation-++-left permutation-empty cs = permutation-same cs
permutation-++-left (permutation-cons a p) cs =
  permutation-cons a (permutation-++-left p cs)
permutation-++-left (permutation-swap a b l) cs =
  permutation-swap a b (l ++ cs)
permutation-++-left (permutation-compose p1 p2) cs =
  permutation-compose
    (permutation-++-left p1 cs)
    (permutation-++-left p2 cs)

permutation-++-swap :
  (a : A) (as bs : List A) -> Permutation A ((a :: as) ++ bs) (as ++ (a :: bs))
permutation-++-swap {A = A} a [] bs         = permutation-same (a :: bs)
permutation-++-swap {A = A} a (a2 :: as) bs =
  permutation-compose
    (permutation-swap a a2 (as ++ bs))
    (permutation-cons a2 (permutation-++-swap a as bs))

--permutation-++-flip : (as bs : List A) -> Permutation A (as ++ bs) (bs ++ as)
--permutation-++-flip []        bs = permutation-== (sym ++-right-[] )
--permutation-++-flip (a :: as) bs = ?
--  where
--  p1 : Permutation A (a :: (as ++ bs)) (a :: (bs ++ as))
--  p1 = permutation-cons a (permutation-++-flip as bs)
--
--  p2 : Permutation A (a :: (bs ++ as)) ((bs ++ [a]) ++ as)
--  p2 = permutation-cons a (permutation-++-flip as bs)


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

-- AtIndex and Contains

AtIndex : Nat -> List A -> A -> Type _
AtIndex n       []        x = Lift _ Bot
AtIndex zero    (a :: as) x = x == a
AtIndex (suc n) (_ :: as) x = AtIndex n as x

contains : A -> Pred (List A) _
contains {A = A} x as = Σ[ n ∈ Nat ] (AtIndex n as x)
-- contains {A = A} a s = Σ[ l ∈ List A ] (Σ[ r ∈ List A ] (l ++ [ a ] ++ r == as))

[]-¬contains : {x : A} -> ¬ (contains x [])
[]-¬contains ()

cons-contains : (a : A) {x : A} {as : List A} -> contains x as -> contains x (a :: as)
cons-contains a (n , p) = (suc n , p)

contains-!= : {x a : A} -> {as : List A} -> x != a -> contains x (a :: as) -> contains x as
contains-!= ¬p (0     , p)  = bot-elim (¬p p)
contains-!= ¬p (suc n , ai) = (n , ai)


list∈ : List A -> Pred A _
list∈ as a = contains a as

split-contains-cons : {x : A} {a : A} {as : List A} -> contains x (a :: as)
                      -> (x == a) ⊎ contains x as
split-contains-cons (0     , p)  = (inj-l p)
split-contains-cons (suc n , ai) = (inj-r (n , ai))

split-contains-++ : {x : A} (as bs : List A) -> contains x (as ++ bs)
                     -> contains x as ⊎ contains x bs
split-contains-++ []        bs c            = inj-r c
split-contains-++ (a :: as) bs (0 , p)      = inj-l (0 , p)
split-contains-++ (a :: as) bs (suc n , ai) =
  ⊎-map-left (cons-contains a) (split-contains-++ as bs (n , ai))

++-contains-left : {x : A} (as bs : List A) -> contains x as -> contains x (as ++ bs)
++-contains-left (a :: as) bs (0     , p) = (0 , p)
++-contains-left (a :: as) bs (suc n , p) =
  cons-contains a (++-contains-left as bs (n , p))

++-contains-right : {x : A} (as bs : List A) -> contains x bs -> contains x (as ++ bs)
++-contains-right []        bs c = c
++-contains-right (a :: as) bs c =
  cons-contains a (++-contains-right as bs c)



map-at-index : (f : A -> B) {n : Nat} (as : List A) {x : A}
               -> AtIndex n as x -> AtIndex n (map f as) (f x)
map-at-index f {n = zero}  (a :: as) p = cong f p
map-at-index f {n = suc n} (a :: as) p = map-at-index f as p

map-contains : (f : A -> B) (as : List A) {x : A} -> contains x as -> contains (f x) (map f as)
map-contains f as (n , ai) = (n , map-at-index f as ai)

map-at-index' : (f : A -> B) {n : Nat} (as : List A) {y : B}
               -> AtIndex n (map f as) y
               -> Σ[ x ∈ A ] (AtIndex n as x × (f x == y))
map-at-index' f {n = zero}  (a :: as) p = (a , refl , sym p)
map-at-index' f {n = suc n} (a :: as) p = map-at-index' f as p

map-at-index-inj : (f : A -> B) {n : Nat} (as : List A) {x : A}
                   -> AtIndex n (map f as) (f x)
                   -> Injective f
                   -> AtIndex n as x
map-at-index-inj f {n} as ai inj-f =
  transport (\i -> AtIndex n as (inj-f (snd (snd res)) i)) (fst (snd res))
  where
  res = map-at-index' f as ai

map-contains' : (f : A -> B) (as : List A) {y : B}
                -> contains y (map f as)
                -> Σ[ x ∈ A ] (contains x as × (f x == y))
map-contains' {A = A} f as {y} (n , ai) = handle (map-at-index' f as ai)
  where
  handle : Σ[ x ∈ A ] (AtIndex n as x × (f x == y))
           -> Σ[ x ∈ A ] (contains x as × (f x == y))
  handle  (x , ai' , p) =  x , (n , ai') , p


permutation-contains : {as bs : List A} -> Permutation A as bs -> (list∈ as ⊆ list∈ bs)
permutation-contains (permutation-empty)      ()
permutation-contains (permutation-cons a p)   (suc n , ai) =
  cons-contains a (permutation-contains p (n , ai))
permutation-contains (permutation-cons a _)   (zero        , p) = (zero , p)
permutation-contains (permutation-swap a b l) (zero        , p) = (suc zero , p)
permutation-contains (permutation-swap a b l) (suc zero    , p) = (zero , p)
permutation-contains (permutation-swap a b l) (suc (suc n) , p) = (suc (suc n) , p)
permutation-contains (permutation-compose p1 p2) c =
  (permutation-contains p2 (permutation-contains p1 c))


module _ where
  private
    lift-:: : (a : A) {as : List A} -> (Σ A (list∈ as)) -> (Σ A (list∈ (a :: as)))
    lift-:: a (a2 , c) = a2 , cons-contains a c

  contains-map : (as : List A) -> List (Σ A (list∈ as))
  contains-map [] = []
  contains-map (a :: as) = (a , zero , refl) :: (map (lift-:: a) (contains-map as))

  contains-map-fst : (as : List A) -> map fst (contains-map as) == as
  contains-map-fst []        = refl
  contains-map-fst (a :: as) =
    cong (a ::_) (double-map fst (lift-:: a) (contains-map as) >=> (contains-map-fst as))

ContainsOnly : (Pred A ℓ) -> Pred (List A) _
ContainsOnly P as = (list∈ as) ⊆ P

ContainsAll : (Pred A ℓ) -> Pred (List A) _
ContainsAll P as = P ⊆ (list∈ as)

ContainsExactly : (Pred A ℓ) -> Pred (List A) _
ContainsExactly P as = (ContainsOnly P as) × (ContainsAll P as)

contains-only->list : {P : Pred A ℓ} (as : List A) -> ContainsOnly P as -> List (Σ A P)
contains-only->list as c->p = map (\(a , c) -> a , (c->p c)) (contains-map as)

NoDuplicates : (Pred (List A) _)
NoDuplicates {A = A} [] = Lift (levelOf A) Top
NoDuplicates (a :: as) = (¬ (contains a as) × NoDuplicates as)

no-duplicates-permutation :
  {as bs : List A} -> NoDuplicates as -> Permutation A as bs -> NoDuplicates bs
no-duplicates-permutation nd (permutation-empty) = nd
no-duplicates-permutation (¬c , nd) (permutation-cons a p) =
  (\c -> ¬c (permutation-contains (permutation-flip p) c)) ,
  no-duplicates-permutation nd p
no-duplicates-permutation (¬ca , ¬cb , nd) (permutation-swap a b l) = (¬cb' , ¬ca' , nd)
  where
  ¬cb' : ¬ (contains b (a :: l))
  ¬cb' (zero  , p) = ¬ca (zero , (sym p))
  ¬cb' (suc n , p) = ¬cb (n , p)

  ¬ca' : ¬ (contains a l)
  ¬ca' c = ¬ca (cons-contains b c)
no-duplicates-permutation nd (permutation-compose p1 p2) =
  no-duplicates-permutation (no-duplicates-permutation nd p1) p2

map-no-duplicates : {f : A -> B} {as : List A} -> Injective f
                    -> NoDuplicates as -> NoDuplicates (map f as)
map-no-duplicates {as = []} inj-f nd = lift tt
map-no-duplicates {A = A} {f = f} {as = a :: as} inj-f (¬c , nd) = (¬c' , map-no-duplicates inj-f nd)
  where
  ¬c' : ¬ (contains (f a) (map f as))
  ¬c' (n , ai-f-as) = ¬c c-a
    where
    res2 : Σ[ x ∈ A ] (AtIndex n as x × (f x == f a))
    res2 = map-at-index' f as ai-f-as

    x = fst res2
    path : x == a
    path = inj-f (snd (snd res2))

    c-x : contains x as
    c-x = n , (fst (snd res2))

    c-a : contains a as
    c-a = (transport (\i -> (contains (path i) as)) c-x)

++-no-duplicates :
  {as bs : List A} -> NoDuplicates as -> NoDuplicates bs
  -> (list∈ as ⊆ Comp (list∈ bs))
  -> NoDuplicates (as ++ bs)
++-no-duplicates {as = []}      nd-a nd-b f = nd-b
++-no-duplicates {as = a :: as} {bs = bs} (¬c , nd-a) nd-b f =
  (¬c' , ++-no-duplicates nd-a nd-b f')
  where
  ¬c' : ¬ (contains a (as ++ bs))
  ¬c' c = handle (split-contains-++ as bs c)
    where
    handle : contains a as ⊎ contains a bs -> Bot
    handle (inj-l ca) = ¬c ca
    handle (inj-r cb) = (f (0 , refl) cb)

  f' : (list∈ as ⊆ Comp (list∈ bs))
  f' ca cb = f (cons-contains a ca) cb


ContainsExactlyOnce : ∀ {ℓ} -> Pred A ℓ -> Pred (List A) _
ContainsExactlyOnce P = ContainsExactly P ∩ NoDuplicates

-- Subsequences
data Subsequence (A : Type ℓ) : (as bs : List A) -> Type ℓ where
  subsequence-empty : Subsequence A [] []
  subsequence-keep : {as bs : List A} (a : A) -> Subsequence A as bs -> Subsequence A (a :: as) (a :: bs)
  subsequence-drop : {as bs : List A} (a : A) -> Subsequence A as bs -> Subsequence A as (a :: bs)

subsequence-same : (as : List A) -> Subsequence A as as
subsequence-same []        = subsequence-empty
subsequence-same (a :: as) = subsequence-keep a (subsequence-same as)

subsequence-[] : (as : List A) -> Subsequence A [] as
subsequence-[] []        = subsequence-empty
subsequence-[] (a :: as) = subsequence-drop a (subsequence-[] as)

trans-subsequence : Transitive (Subsequence A)
trans-subsequence as (subsequence-drop a bs) =
  subsequence-drop a (trans-subsequence as bs)
trans-subsequence subsequence-empty subsequence-empty = subsequence-empty
trans-subsequence (subsequence-keep a as) (subsequence-keep a bs) =
  subsequence-keep a (trans-subsequence as bs)
trans-subsequence (subsequence-drop a as) (subsequence-keep a bs) =
  subsequence-drop a (trans-subsequence as bs)

subsequence-length≤ : {as bs : List A} -> Subsequence A as bs -> length as ≤ length bs
subsequence-length≤ subsequence-empty = zero-≤
subsequence-length≤ (subsequence-keep a s) = suc-≤ (subsequence-length≤ s)
subsequence-length≤ (subsequence-drop a s) = right-suc-≤ (subsequence-length≤ s)

subsequence-length≥ : {as bs : List A} -> Subsequence A as bs -> length as ≥ length bs -> as == bs
subsequence-length≥ subsequence-empty      lt = refl
subsequence-length≥ (subsequence-keep a s) lt = cong (a ::_) (subsequence-length≥ s (pred-≤ lt))
subsequence-length≥ (subsequence-drop a s) lt =
  bot-elim (transport (sym ≮==≥) (subsequence-length≤ s) lt)

antisym-subsequence : Antisymmetric (Subsequence A)
antisym-subsequence s1 s2 = subsequence-length≥ s1 (subsequence-length≤ s2)

-- Subset
Subset : (A : Type ℓ) (as bs : List A) -> Type ℓ
Subset A as bs = Σ[ cs ∈ List A ] (Permutation A as cs × Subsequence A cs bs)

subset-[] : (as : List A) -> Subset A [] as
subset-[] as = ([] , permutation-empty , subsequence-[] as)


subset-keep : {as bs : List A} -> (a : A) -> Subset A as bs -> Subset A (a :: as) (a :: bs)
subset-keep a (cs , p , ss) = (a :: cs , (permutation-cons a p) , (subsequence-keep a ss))
subset-drop : {as bs : List A} -> (a : A) -> Subset A as bs -> Subset A as (a :: bs)
subset-drop a (cs , p , ss) = (cs , p , (subsequence-drop a ss))

subset-perm-left : {as bs cs : List A} -> Permutation A as bs -> Subset A bs cs -> Subset A as cs
subset-perm-left p1 (l , p2 , ss) = (l , (permutation-compose p1 p2) , ss)

module _ {A : Type ℓ} where
  private
    Subset' : (A : Type ℓ) (as bs : List A) -> Type ℓ
    Subset' A as bs = Σ[ cs ∈ List A ] (Subsequence A as cs × Permutation A cs bs)
    subset'-[] : (as : List A) -> Subset' A [] as
    subset'-[] as = (as , subsequence-[] as , permutation-same as)

    subset-subsequence : {as bs cs : List A} -> Subset A as bs -> Subsequence A bs cs -> Subset A as cs
    subset-subsequence (l , p , ss1) ss2 = (l , p , trans-subsequence ss1 ss2)

    subsequence->subset : {as bs : List A} -> Subsequence A as bs -> Subset A as bs
    subsequence->subset ss = (_ , permutation-same _ , ss)

    rec : {as bs cs : List A} -> Subsequence A as bs -> Permutation A bs cs
          -> Subset A as cs
    rec {as} {bs} {cs} ss (permutation-compose {as2 = as2} p1 p2) = subset-perm-left p1' res2
      where
      res1 : Subset A as as2
      res1 = rec ss p1
      ds : List A
      ds = fst res1
      p1' : Permutation A as ds
      p1' = fst (snd res1)
      ss1 : Subsequence A ds as2
      ss1 = snd (snd res1)

      res2 : Subset A ds cs
      res2 = rec ss1 p2

    rec (subsequence-keep a ss) (permutation-cons a p) = subset-keep a (rec ss p)
    rec (subsequence-drop a ss) (permutation-cons a p) = subset-drop a (rec ss p)
    rec (subsequence-keep a (subsequence-keep b ss)) (permutation-swap a b _) =
      subset-perm-left
        (permutation-swap a b _)
        (subset-keep b (subset-keep a (subsequence->subset ss)))
    rec (subsequence-keep a (subsequence-drop b ss)) (permutation-swap a b _) =
      (subset-drop b (subset-keep a (subsequence->subset ss)))
    rec (subsequence-drop a (subsequence-keep b ss)) (permutation-swap a b _) =
      (subset-keep b (subset-drop a (subsequence->subset ss)))
    rec (subsequence-drop a (subsequence-drop b ss)) (permutation-swap a b _) =
      (subset-drop b (subset-drop a (subsequence->subset ss)))
    rec subsequence-empty permutation-empty = subset-[] _

  subset'->subset : {as bs : List A} -> Subset' A as bs -> Subset A as bs
  subset'->subset (_ , ss , p) = rec ss p


  trans-subset : Transitive (Subset A)
  trans-subset {as} {bs} {cs} (ds1 , p1 , ss1) (ds2 , p2 , ss2) =
    subset-perm-left p1 (subset-subsequence (subset'->subset (_ , ss1 , p2)) ss2)


subset-perm-right : {as bs cs : List A} -> Subset A as bs -> Permutation A bs cs -> Subset A as cs
subset-perm-right s p = trans-subset s (_ , p , subsequence-same _)

subset-length≤ : {as bs : List A} -> Subset A as bs -> length as ≤ length bs
subset-length≤ {as = as} {bs = bs} (cs , p , ss) =
  transport (\i -> (permutation-length== p (~ i)) ≤ length bs) (subsequence-length≤ ss)

subset-length≥ : {as bs : List A} -> Subset A as bs -> length as ≥ length bs
                 -> Permutation A as bs
subset-length≥ {A = A} {as = as} {bs = bs} (cs , p , ss) lt =
  transport (\i -> Permutation A as (cs==bs i)) p
  where
  cs==bs : cs == bs
  cs==bs = subsequence-length≥ ss (transport (\i -> (permutation-length== p i) ≥ length bs) lt)

subsets->perm : {as bs : List A} -> Subset A as bs -> Subset A bs as -> Permutation A as bs
subsets->perm s1 s2 = subset-length≥ s1 (subset-length≤ s2)

-- Subsequences and Subsets and contains

subsequence-contains : {as bs : List A} -> Subsequence A as bs -> (list∈ as ⊆ list∈ bs)
subsequence-contains subsequence-empty      ()
subsequence-contains (subsequence-keep a s) (0     , p) = (0 , p)
subsequence-contains (subsequence-keep a s) (suc n , p) =
  cons-contains a (subsequence-contains s (n , p))
subsequence-contains (subsequence-drop a s) c =
  cons-contains a (subsequence-contains s c)

subset-contains : {as bs : List A} -> Subset A as bs -> (list∈ as ⊆ list∈ bs)
subset-contains (_ , p , ss) = subsequence-contains ss ∘ permutation-contains p

take : Nat -> List A -> List A
take zero    _         = []
take (suc n) []        = []
take (suc n) (a :: as) = a :: (take n as)

drop : Nat -> List A -> List A
drop zero    as        = as
drop (suc n) []        = []
drop (suc n) (a :: as) = drop n as

remove-at-index : Nat -> List A -> List A
remove-at-index n       [] = []
remove-at-index zero    (a :: as) = as
remove-at-index (suc n) (a :: as) = a :: (remove-at-index n as)

at-index->path : {n : Nat} {as : List A} {x : A} -> AtIndex n as x
                       -> take n as ++ [ x ] ++ drop (suc n) as == as
at-index->path {n = zero}  {a :: as} {x} p = \i -> p i :: as
at-index->path {n = suc n} {a :: as} {x} p =
  cong (a ::_) (at-index->path p)

contains->path : {x : A} {as : List A} -> (c : contains x as)
                 -> take ⟨ c ⟩ as ++ [ x ] ++ drop (suc ⟨ c ⟩) as == as
contains->path (n , p) = at-index->path p

contains->subset : {as bs : List A} -> (list∈ as ⊆ list∈ bs) -> NoDuplicates as -> Subset A as bs
contains->subset {as = []} f nd = subset-[] _
contains->subset {A = A} {a :: as} {bs} f (¬c-a-as , nd) =
  subset-perm-right (subset-keep a (contains->subset g nd)) p-bs'
  where
  c-a-bs : contains a bs
  c-a-bs = f (0 , refl)

  index : Nat
  index = fst c-a-bs

  --bs' : List A
  --bs' = remove-at-index index bs

  l = take index bs
  r = drop (suc index) bs
  bs' = l ++ r

  pre-p-bs' : Permutation A ([ a ] ++ (l ++ r)) (l ++ ([ a ] ++ r))
  pre-p-bs' =
    permutation-compose
      (permutation-== (sym (++-assoc {a = [ a ]} {l} {r})))
      (permutation-compose
        (permutation-++-left (permutation-snoc a l) r)
        (permutation-== (++-assoc {a = l} {[ a ]} {r})))

  p-bs' : Permutation A (a :: bs') bs
  p-bs' = permutation-compose pre-p-bs' (permutation-== (contains->path c-a-bs))

  g : (list∈ as ⊆ list∈ bs')
  g {a = x} c = handle (split-contains-cons
                         (permutation-contains (permutation-flip p-bs')
                                               (f (cons-contains a c))))
    where
    handle : (x == a ⊎ contains x bs') -> contains x bs'
    handle (inj-r c') = c'
    handle (inj-l p) = bot-elim (¬c-a-as (transport (\i -> contains (p i) as) c))

contains-exactly-once->permutation :
  {P : Pred A ℓ} {as bs : List A}
  -> ContainsExactlyOnce P as -> ContainsExactlyOnce P bs -> Permutation A as bs
contains-exactly-once->permutation ((co-a , ca-a) , nd-a) ((co-b , ca-b) , nd-b) =
  subsets->perm (contains->subset (ca-b ∘ co-a) nd-a)
                (contains->subset (ca-a ∘ co-b) nd-b)

-- Cartesian Product

cartesian-product : List A -> List B -> List (A × B)
cartesian-product [] bs = []
cartesian-product (a :: as) bs = map (a ,_) bs ++ cartesian-product as bs

cartesian-product' : (A -> B -> C) -> List A -> List B -> List C
cartesian-product' f as bs = map (\ (a , b) -> f a b) (cartesian-product as bs)

cartesian-product-contains : {x : A} {y : B} (as : List A) (bs : List B)
                             -> contains x as -> contains y bs
                             -> contains (x , y) (cartesian-product as bs)
cartesian-product-contains {A = A} {B = B} {x} {y} (a :: as) bs (0     , p) cb =
  transport (\i -> contains (p (~ i) , y) ((map (a ,_) bs) ++ cartesian-product as bs)) c
  where

  c : contains (a , y) ((map (a ,_) bs) ++ cartesian-product as bs)
  c = ++-contains-left (map (a ,_) bs) (cartesian-product as bs)
                       (map-contains (a ,_) bs cb)
cartesian-product-contains (a :: as) bs (suc n , p) cb =
  ++-contains-right (map (a ,_) bs) (cartesian-product as bs)
                    (cartesian-product-contains as bs (n , p) cb)

private
  pair-injective-left : (a : A) -> Injective (\ (b : B) -> (a , b))
  pair-injective-left a p = cong snd p

cartesian-product-contains' : {x : A} {y : B} (as : List A) (bs : List B)
                              -> contains (x , y) (cartesian-product as bs)
                              -> (contains x as × contains y bs)
cartesian-product-contains' {B = B} {x = x} {y = y} (a :: as) bs c =
  handle (split-contains-++ (map (a ,_) bs) (cartesian-product as bs) c)
  where
  handle : (contains (x , y) (map (a ,_) bs) ⊎ contains (x , y) (cartesian-product as bs))
           -> (contains x (a :: as) × contains y bs)
  handle (inj-l (n , ai)) = handle2 n bs ai
    where
    handle2 : (n : Nat) -> (bs : List B)
              -> AtIndex n (map (a ,_) bs) (x , y)
              -> (contains x (a :: as) × contains y bs)
    handle2 0       (b :: bs) p = (0 , cong fst p) , (0 , cong snd p)
    handle2 (suc n) (b :: bs) p = handle3 (handle2 n bs p)
      where
      handle3 : (contains x (a :: as) × contains y bs)
                -> (contains x (a :: as) × contains y (b :: bs))
      handle3 (c1 , c2) = c1 , cons-contains b c2

  handle (inj-r c) = handle2 (cartesian-product-contains' as bs c)
    where
    handle2 : (contains x as × contains y bs)
              -> (contains x (a :: as) × contains y bs)
    handle2 (c1 , c2) = cons-contains a c1 , c2

cartesian-product-no-duplicates :
  {as : List A} {bs : List B} -> NoDuplicates as -> NoDuplicates bs
  -> NoDuplicates (cartesian-product as bs)
cartesian-product-no-duplicates {as = []} nd-a nd-b = lift tt
cartesian-product-no-duplicates {A = A} {B = B} {as = a :: as} {bs} (¬c-a , nd-a) nd-b =
  ++-no-duplicates nd-a' (cartesian-product-no-duplicates nd-a nd-b) ¬c-both
  where

  nd-a' : NoDuplicates (map (a ,_) bs)
  nd-a' = map-no-duplicates (pair-injective-left a) nd-b

  a-path : {x : A} {y : B} (bs : List B) -> contains (x , y) (map (a ,_) bs) -> x == a
  a-path (b :: bs) (0 , p)     = cong fst p
  a-path (b :: bs) (suc n , p) = a-path bs (n , p)


  ¬c-both : {x : A × B} -> contains x (map (a ,_) bs) -> contains x (cartesian-product as bs) -> Bot
  ¬c-both {x = (xa , xb)} cb c-prod = ¬c-a c-a
    where
    xa==a : xa == a
    xa==a = a-path bs cb

    c-xa : (contains xa as)
    c-xa = fst (cartesian-product-contains' as bs c-prod)

    c-a : (contains a as)
    c-a = transport (\i -> contains (xa==a i) as) c-xa

cartesian-product'-no-duplicates :
   {f : A -> B -> C} (as : List A) (bs : List B)
   -> Injective2 f -> NoDuplicates as -> NoDuplicates bs
   -> NoDuplicates (cartesian-product' f as bs)
cartesian-product'-no-duplicates {f = f} as bs inj-f nd-a nd-b =
  map-no-duplicates inj-f' (cartesian-product-no-duplicates nd-a nd-b)
  where
  inj-f' : Injective (\ (a , b) -> f a b)
  inj-f' {x1 , y1} {x2 , y2} p i = fst (inj-f p) i , snd (inj-f p) i


module _ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where
  Sorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
  Sorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
  Sorted (a :: as) = ContainsOnly (a ≤_) as × Sorted as

  SemiSorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
  SemiSorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
  SemiSorted (a :: as) = ContainsOnly ((a ≤_) ∪ (a ==_)) as × SemiSorted as

reverse-acc : List A -> List A -> List A
reverse-acc []        acc = acc
reverse-acc (a :: as) acc = reverse-acc as (a :: acc)

reverse-acc-permutation : (as bs : List A) -> Permutation A (as ++ bs) (reverse-acc as bs)
reverse-acc-permutation [] bs = permutation-same bs
reverse-acc-permutation (a :: as) bs =
  permutation-compose
    (permutation-++-swap a as bs)
    (reverse-acc-permutation as (a :: bs))

reverse : List A -> List A
reverse as = reverse-acc as []

reverse-permutation : (as : List A) -> Permutation A as (reverse as)
reverse-permutation as =
  permutation-compose
    (permutation-== (sym ++-right-[]))
    (reverse-acc-permutation as [])
