{-# OPTIONS --cubical --safe --exact-split #-}

module list where

open import base
open import equality-path
open import functions
open import monoid
open import nat
open import order
open import order.instances.nat
open import quotient
open import relation hiding (acc)
open import ring.implementations
open import sigma.base
open import sum

open import list.append public
open import list.base public
open import list.permutation public

private
  variable
    ℓ : Level
    A B C D : Type ℓ


double-map : (f : B -> C) (g : A -> B) (as : List A)
             -> map f (map g as) == map (f ∘ g) as
double-map {A = A} f g [] = refl
double-map {A = A} f g (a :: as) = cong ((f (g a)) ::_) (double-map f g as)

map-identity : (as : List A) -> map (\x -> x) as == as
map-identity [] = refl
map-identity (a :: as) = cong (a ::_) (map-identity as)

map-inject-++ : (f : A -> B) {a1 a2 : List A} -> map f (a1 ++ a2) == (map f a1) ++ (map f a2)
map-inject-++ f {[]} = refl
map-inject-++ f {e :: a1} {a2} = cong (\x -> f e :: x) (map-inject-++ f {a1} {a2})

map-preserves-length : {f : A -> B} (as : List A) -> length (map f as) == length as
map-preserves-length [] = refl
map-preserves-length (a :: as) = cong suc (map-preserves-length as)

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

AtIndex : Nat -> List A -> A -> Type (levelOf A)
AtIndex n       []        x = Lift _ Bot
AtIndex zero    (a :: as) x = x == a
AtIndex (suc n) (_ :: as) x = AtIndex n as x

contains : A -> Pred (List A) _
contains {A = A} x as = Σ[ n ∈ Nat ] (AtIndex n as x)

[]-¬contains : {x : A} -> ¬ (contains x [])
[]-¬contains ()

cons-contains : (a : A) {x : A} {as : List A} -> contains x as -> contains x (a :: as)
cons-contains a (n , p) = (suc n , p)

contains-!= : {x a : A} -> {as : List A} -> x != a -> contains x (a :: as) -> contains x as
contains-!= ¬p (0     , p)  = bot-elim (¬p p)
contains-!= ¬p (suc n , ai) = (n , ai)

same-at-index : {i : Nat} {a1 a2 : A} -> (as : List A) -> AtIndex i as a1 -> AtIndex i as a2 -> a1 == a2
same-at-index {i = zero}  (a :: as) p1 p2 = p1 >=> (sym p2)
same-at-index {i = suc i} (a :: as) p1 p2 = same-at-index as p1 p2

same-at-index' : {i j : Nat} {a1 a2 : A} -> (as : List A)
                 -> AtIndex i as a1 -> AtIndex j as a2
                 -> i == j -> a1 == a2
same-at-index' {a1 = a1} as p1 p2 path =
  same-at-index {a1 = a1} as (transport (\j -> AtIndex (path j) as a1) p1) p2

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

++-at-index-left : {i : Nat} {x : A} (as bs : List A) -> AtIndex i as x -> AtIndex i (as ++ bs) x
++-at-index-left {i = 0}     (a :: as) bs p = p
++-at-index-left {i = suc i} (a :: as) bs ai = ++-at-index-left as bs ai

++-at-index-right : {i : Nat} {x : A} (as bs : List A) -> AtIndex i bs x
                    -> AtIndex (length as +' i) (as ++ bs) x
++-at-index-right []        bs ai = ai
++-at-index-right (a :: as) bs ai = (++-at-index-right as bs ai)


++-contains-left : {x : A} (as bs : List A) -> contains x as -> contains x (as ++ bs)
++-contains-left as bs (n , ai) = (n , ++-at-index-left as bs ai)

++-contains-right : {x : A} (as bs : List A) -> contains x bs -> contains x (as ++ bs)
++-contains-right as bs (i , ai) = (length as +' i , ++-at-index-right as bs ai)


++-at-index-left⁻ : {i : Nat} {x : A} (as bs : List A) -> i < (length as)
                     -> AtIndex i (as ++ bs) x
                     -> AtIndex i as x
++-at-index-left⁻             []        bs lt ai = bot-elim (zero-≮ lt)
++-at-index-left⁻ {i = zero}  (a :: as) bs lt ai = ai
++-at-index-left⁻ {i = suc i} (a :: as) bs lt ai = ++-at-index-left⁻ as bs (pred-≤ lt) ai

++-at-index-right⁻ :
  {ℓ : Level} {A : Type ℓ} {i : Nat} {x : A}
  (as bs : List A) -> (lt : (length as) ≤ i) -> AtIndex i (as ++ bs) x -> AtIndex ⟨ lt ⟩ bs x
++-at-index-right⁻ {i = i} {x = x} [] bs (k , path) ai =
  transport (\j -> AtIndex (full-path j) bs x) ai
  where
  full-path : i == k
  full-path = sym path >=> +'-right-zero
++-at-index-right⁻ {i = zero}  (a :: as) bs lt ai = bot-elim (zero-≮ lt)
++-at-index-right⁻ {i = suc i} (a :: as) bs lt ai =
  ++-at-index-right⁻ as bs (pred-≤ lt) ai




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

-- NoDuplicates based on uniqueness of indices
NoDuplicatesIndex : Pred (List A) _
NoDuplicatesIndex as = ∀ {a} -> (c1 c2 : contains a as) -> ⟨ c1 ⟩ == ⟨ c2 ⟩

no-duplicates-index->no-duplicates : {as : List A} -> NoDuplicatesIndex as -> NoDuplicates as
no-duplicates-index->no-duplicates {as = []}      _ = lift tt
no-duplicates-index->no-duplicates {as = a :: as} f = ¬ca , nd-rec
  where
  ¬ca : ¬(contains a as)
  ¬ca (n , at-n) = zero-suc-absurd (f (0 , refl) (suc n , at-n))

  nd-rec : NoDuplicates as
  nd-rec = no-duplicates-index->no-duplicates g
    where
    g : ∀ {a} -> (c1 c2 : contains a as) -> ⟨ c1 ⟩ == ⟨ c2 ⟩
    g (n , at-n) (m , at-m) = cong pred (f (suc n , at-n) (suc m , at-m))

no-duplicates->no-duplicates-index : {as : List A} -> NoDuplicates as -> NoDuplicatesIndex as
no-duplicates->no-duplicates-index {as = []}      _ {a} c1 c2 = bot-elim ([]-¬contains {x = a} c1)
no-duplicates->no-duplicates-index {as = a :: as} (¬c-a , nd-as) (zero , _) (zero , _) = refl
no-duplicates->no-duplicates-index {as = a :: as} (¬c-a , nd-as) (zero , a-path) (suc m , at-m) =
  bot-elim (¬c-a (transport (\i -> (contains (a-path i) as))  (m , at-m)))
no-duplicates->no-duplicates-index {as = a :: as} (¬c-a , nd-as) (suc n , at-n) (zero , a-path) =
  bot-elim (¬c-a (transport (\i -> (contains (a-path i) as))  (n , at-n)))
no-duplicates->no-duplicates-index {as = a :: as} (¬c-a , nd-as) (suc n , at-n) (suc m , at-m) =
  cong suc (no-duplicates->no-duplicates-index nd-as (n , at-n) (m , at-m))


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

cartesian-product-right-[] : (as : List A) -> cartesian-product {B = B} as [] == []
cartesian-product-right-[] []        = refl
cartesian-product-right-[] (a :: as) = cartesian-product-right-[] as


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


cartesian-product-at-index : {ix iy : Nat} {x : A} {y : B} (as : List A) (bs : List B)
                             -> AtIndex ix as x -> AtIndex iy bs y
                             -> AtIndex (ix *' length bs +' iy) (cartesian-product as bs) (x , y)
cartesian-product-at-index {A = A} {B = B} {zero}   {iy} {x} {y} (a :: as) bs aix aiy =
  transport (\i -> AtIndex iy (cartesian-product (a :: as) bs) (aix (~ i) , y)) answer
  where

  answer : AtIndex iy (cartesian-product (a :: as) bs) (a , y)
  answer =
    ++-at-index-left (map (a ,_) bs) (cartesian-product as bs) (map-at-index (a ,_) bs aiy)

cartesian-product-at-index {A = A} {B = B} {suc ix} {iy} {x} {y} (a :: as) bs aix aiy =
  transport (\i -> AtIndex (index-path i) (cartesian-product (a :: as) bs) (x , y)) answer
  where
  index-path : ((length (map (a ,_) bs)) +' (ix *' length bs +' iy)) == (suc ix *' length bs +' iy)
  index-path =
    begin
      ((length (map (a ,_) bs)) +' (ix *' length bs +' iy))
    ==< +'-left (map-preserves-length bs) >
      (length bs +' (ix *' length bs +' iy))
    ==< sym (+'-assoc {length bs} {_} {iy}) >
      (suc ix *' length bs +' iy)
    end

  answer : AtIndex ((length (map (a ,_) bs)) +' (ix *' length bs +' iy))
                   (cartesian-product (a :: as) bs)
                   (x , y)
  answer =
    ++-at-index-right (map (a ,_) bs) (cartesian-product as bs)
                      (cartesian-product-at-index as bs aix aiy)

cartesian-product-at-index' : {i : Nat} {x : A} {y : B} (as : List A) (bs : List B)
                              -> AtIndex i (cartesian-product as bs) (x , y)
                              -> (pos-lb : Pos' (length bs))
                              -> (AtIndex (quotient  i ((length bs) , pos-lb)) as x ×
                                  AtIndex (remainder i ((length bs) , pos-lb)) bs y)
cartesian-product-at-index' {i = i} {x} {y} [] bs ai _ =
  bot-elim (Lift.lower (transport (\j -> AtIndex i [] (x , y)) ai))


cartesian-product-at-index' {i = i} {x} {y} (a :: as) bs ai pos-lb = handle (split-nat< i (length bs))
  where
  lb = ((length bs) , pos-lb)
  l = (map (a ,_) bs)
  r = (cartesian-product as bs)
  handle : ((i < length bs) ⊎ (i ≥ (length bs))) ->
           (AtIndex (quotient i lb) (a :: as) x ×
            AtIndex (remainder i lb) bs y)
  handle (inj-l i<lb) =
    transport (\j -> AtIndex (0==q j) (a :: as) x × AtIndex (i==r j) bs y)
              (ai-as' , ai-bs')
    where
    i<ll : i < (length l)
    i<ll = transport (\j -> i < (map-preserves-length {f = a ,_} bs (~ j))) i<lb

    ai2 : AtIndex i l (x , y)
    ai2 = ++-at-index-left⁻ l r i<ll ai

    ai-as' : AtIndex 0 (a :: as) x
    ai-as' = sym (cong fst (snd (snd (map-at-index' (a ,_) bs ai2))))

    ai-bs' : AtIndex i bs y
    ai-bs' = transport (\j -> AtIndex i bs (cong snd (snd p) j)) (fst p)
      where
      p = (snd (map-at-index' (a ,_) bs ai2))

    0==q : 0 == quotient i lb
    0==q = sym (small-quotient lb i<lb)

    i==r : i == remainder i lb
    i==r = sym (small-remainder lb i<lb)

  handle (inj-r i≥lb) =
    transport (\j -> AtIndex (q'==q j) (a :: as) x × AtIndex (r'==r j) bs y)
              rec
    where
    k = ⟨ i≥lb ⟩

    i≥ll : i ≥ (length l)
    i≥ll = transport (\j -> i ≥ (map-preserves-length {f = a ,_} bs (~ j))) i≥lb

    rec : (AtIndex (quotient  k lb) as x ×
           AtIndex (remainder k lb) bs y)
    rec = cartesian-product-at-index' as bs (++-at-index-right⁻ l r i≥ll ai) pos-lb

    q'==q : (suc (quotient k lb)) == (quotient i lb)
    q'==q = sym (large-quotient lb i≥lb)

    r'==r : (remainder k lb) == (remainder i lb)
    r'==r = sym (large-remainder lb i≥lb)



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

cartesian-product-map : (f : (A -> C)) (g : (B -> D)) (as : List A) (bs : List B)
                        -> map (×-map f g) (cartesian-product as bs)
                           == cartesian-product (map f as) (map g bs)
cartesian-product-map f g []        bs = refl
cartesian-product-map f g (a :: as) bs =
  begin
    map h (cartesian-product (a :: as) bs)
  ==< map-inject-++ h {map (a ,_) bs} {cartesian-product as bs} >
    map h (map (a ,_) bs) ++ (map h (cartesian-product as bs))
  ==< cong (_++ (map h (cartesian-product as bs))) (double-map h (a ,_) bs) >
    map (\ b -> (f a , g b)) bs ++ (map h (cartesian-product as bs))
  ==< cong (_++ (map h (cartesian-product as bs))) (sym (double-map (f a ,_) g bs)) >
    map (f a ,_) (map g bs) ++ (map h (cartesian-product as bs))
  ==< cong (map (f a ,_) (map g bs) ++_) (cartesian-product-map f g as bs) >
    map (f a ,_) (map g bs) ++ (cartesian-product (map f as) (map g bs))
  ==<>
    cartesian-product (map f (a :: as)) (map g bs)
  end
  where
  h = (×-map f g)

cartesian-product-ind : (as : List A) -> (bs : List B)
                        -> ((a : A) -> (b : B) -> contains a as -> contains b bs -> C)
                        -> List C
cartesian-product-ind {A = A} {B = B} {C = C} as bs f = map g (contains-map cprod)
  where
  cprod = (cartesian-product as bs)

  g : (Σ[ p ∈ (A × B) ] (contains p cprod)) -> C
  g ((a , b) , c-p) = f a b (proj₁ pair-contains) (proj₂ pair-contains)
    where
    pair-contains = cartesian-product-contains' as bs c-p

cartesian-product-ind' : (A -> B -> C) -> (List A) -> (List B) -> List C
cartesian-product-ind' f as bs = cartesian-product-ind as bs (\ a b _ _ -> f a b)

cartesian-product-ind'-path : {f : A -> B -> C} {as : List A} {bs : List B}
                              -> cartesian-product-ind' f as bs == cartesian-product' f as bs
cartesian-product-ind'-path {A = A} {B = B} {C = C} {f = f} {as} {bs} =
  begin
    cartesian-product-ind' f as bs
  ==<>
    map (\ ((a , b) , _) -> f a b) (contains-map (cartesian-product as bs))
  ==<>
    map (cf ∘ fst) (contains-map (cartesian-product as bs))
  ==< sym (double-map cf fst _) >
    map cf (map fst (contains-map (cartesian-product as bs)))
  ==< cong (map cf) (contains-map-fst _) >
    map cf (cartesian-product as bs)
  ==<>
    cartesian-product' f as bs
  end
  where
  cf : (A × B) -> C
  cf (a , b) = f a b


module _ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where
  Sorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
  Sorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
  Sorted (a :: as) = ContainsOnly (a ≤_) as × Sorted as

  SemiSorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
  SemiSorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
  SemiSorted (a :: as) = ContainsOnly ((a ≤_) ∪ (a ==_)) as × SemiSorted as

map-sorted : {ℓa ℓb ℓ₁ ℓ₂ : Level} {A : Type ℓa} {B : Type ℓb} {f : A -> B}
             {_≤a_ : Rel A ℓ₁} {_≤b_ : Rel B ℓ₂} {as : List A} -> Monotonic _≤a_ _≤b_ f
             -> Sorted _≤a_ as -> Sorted _≤b_ (map f as)
map-sorted {as = []} mono s = lift tt
map-sorted {A = A} {B} {f} {_≤a_} {_≤b_} {(a :: as)} mono (co , s) = co' , map-sorted mono s
  where
  co' : ContainsOnly (f a ≤b_) (map f as)
  co' {b} c = transport (\i -> f a ≤b (path i)) (mono a a2 a≤a2)
    where
    Σa2 : Σ[ a2 ∈ A ] (contains a2 as × f a2 == b)
    Σa2 = map-contains' f as c
    a2 = ⟨ Σa2 ⟩
    path = (snd (snd Σa2))

    a≤a2 : a ≤a a2
    a≤a2 = co (fst (snd Σa2))


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


-- Propositional Count

data Count (A : Type ℓ) : A -> List A -> Nat -> Type ℓ where
  count'-[] : {x : A} -> Count A x [] 0
  count'-== : {x a : A} {as : List A} {n : Nat} -> x == a
              -> Count A x as n
              -> Count A x (a :: as) (suc n)
  count'-!= : {x a : A} {as : List A} {n : Nat} -> x != a
              -> Count A x as n
              -> Count A x (a :: as) n

count-uniqueness : {x : A} {as : List A} {m n : Nat} -> Count A x as m -> Count A x as n -> m == n
count-uniqueness count'-[] count'-[] = refl
count-uniqueness (count'-== _ cm) (count'-== _ cn) = cong suc (count-uniqueness cm cn)
count-uniqueness (count'-!= _ cm) (count'-!= _ cn) = (count-uniqueness cm cn)
count-uniqueness (count'-!= ¬p _) (count'-== p  _) = bot-elim (¬p p)
count-uniqueness (count'-== p  _) (count'-!= ¬p _) = bot-elim (¬p p)
