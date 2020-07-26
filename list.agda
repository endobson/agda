{-# OPTIONS --cubical --safe --exact-split #-}

module list where

open import base
open import relation
open import equality
open import functions
open import monoid
open import nat

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

[]-¬contains : {x : A} -> ¬ (contains x [])
[]-¬contains ([]     , r , p) = zero-suc-absurd (cong length (sym p))
[]-¬contains (_ :: _ , r , p) = zero-suc-absurd (cong length (sym p))

cons-contains : (a : A) {x : A} {as : List A} -> contains x as -> contains x (a :: as)
cons-contains a (l , r , path) = (a :: l , r , cong (a ::_) path)

list∈ : List A -> Pred A _
list∈ as a = contains a as

permutation-contains : {as bs : List A} -> Permutation A as bs -> (list∈ as ⊆ list∈ bs)
permutation-contains (permutation-empty) c-as = bot-elim ([]-¬contains c-as)
permutation-contains (permutation-cons a p) (_ :: l , r , path) =
  cons-contains a (permutation-contains p (l , r , ::-injective path))
permutation-contains (permutation-cons a {as1} {as2} p) ([] , r , path) =
  ([] , as2 , (\i -> (::-injective' path i) :: as2))
permutation-contains (permutation-swap a b p) ([] , r , path) =
  transport (\i -> contains (::-injective' path (~ i)) (b :: a :: p))
            ([ b ] , p , refl)
permutation-contains (permutation-swap a b p) {x} (x2 :: [] , r , path) =
  transport (\i -> contains (::-injective' (::-injective path) (~ i)) (b :: a :: p))
            ([] , a :: p , refl)
permutation-contains (permutation-swap a b p) {x} (_ :: _ :: l , r , path) =
  cons-contains b (cons-contains a (l , r , (::-injective (::-injective path))))
permutation-contains (permutation-compose p1 p2) c =
  (permutation-contains p2 (permutation-contains p1 c))

module _ where
  private
    lift-:: : (a : A) {as : List A} -> (Σ A (list∈ as)) -> (Σ A (list∈ (a :: as)))
    lift-:: a (a2 , l , r , p) = (a2 , a :: l , r , cong (a ::_) p)

  contains-map : (as : List A) -> List (Σ A (list∈ as))
  contains-map [] = []
  contains-map {A = A} (a :: as) = (a , [] , as , refl) :: (map (lift-:: a) (contains-map as))

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

contains-only->list : {P : Pred A ℓ} {as : List A} -> ContainsOnly P as -> List (Σ A P)
contains-only->list {as = as} c->p = map (\(a , c) -> a , (c->p c)) (contains-map as)

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
  ¬cb' ([] , r , p) = ¬ca ([] , l , (\i -> ::-injective' p (~ i) :: l))
  ¬cb' (_ :: l2 , r , p) = ¬cb (l2 , r , ::-injective p)

  ¬ca' : ¬ (contains a l)
  ¬ca' c = ¬ca (cons-contains b c)
no-duplicates-permutation nd (permutation-compose p1 p2) =
  no-duplicates-permutation (no-duplicates-permutation nd p1) p2

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
subsequence-contains subsequence-empty    c = bot-elim ([]-¬contains c)
subsequence-contains {bs = a :: bs} (subsequence-keep a s) ([] , r , p) =
  ([] , bs , (\i -> ::-injective' p i :: bs))
subsequence-contains (subsequence-keep a s) (_ :: l , r , p) =
  cons-contains a (subsequence-contains s (l , r , ::-injective p))
subsequence-contains (subsequence-drop a s) c =
  cons-contains a (subsequence-contains s c)

subset-contains : {as bs : List A} -> Subset A as bs -> (list∈ as ⊆ list∈ bs)
subset-contains (_ , p , ss) = subsequence-contains ss ∘ permutation-contains p
